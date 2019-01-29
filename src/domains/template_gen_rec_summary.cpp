/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   template_gen_rec_summary.cpp
 * Author: sarbojit
 * 
 * Created on 19 March, 2018, 10:19 PM
 */

#define SHOW_TEMPLATE
#include "tpolyhedra_domain.h"

#include "template_gen_rec_summary.h"

void template_gen_rec_summaryt::operator()(const irep_idt &function_name,
  unsigned _domain_number,
  const local_SSAt &SSA,
  exprt &merge_expr,
  bool forward)
{
  domain_number=_domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!
  exprt::operandst pre_guards;

  collect_variables_loop(SSA, forward);
  
  // do not compute summary for entry-point
  if(SSA.goto_function.body.instructions.front().function!=ID__start ||
   options.get_bool_option("preconditions"))
  {
    if(options.get_bool_option("context-sensitive"))
      collect_inout_vars(function_name, SSA, pre_guards, forward);
    else
      collect_variables_inout(SSA,forward);
  }
  
  if(options.get_bool_option("context-sensitive"))
  {
    instantiate_domains_for_rec(SSA, pre_guards);
  }
  // either use standard templates or user-supplied ones
  else if(!instantiate_custom_templates(SSA))
    instantiate_standard_domains(SSA);

#ifdef SHOW_TEMPLATE_VARIABLES
  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(), var_specs, SSA.ns); debug() << eom;
#endif
#ifdef SHOW_TEMPLATE
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns);
  debug()<<"Where:\n";
  for(const exprt& op:merge_expr.operands())
  {
    debug()<<"     "<<from_expr(op)<<eom;
  }
  debug() << eom;
#endif
}

void template_gen_rec_summaryt::create_rb_vars(const local_SSAt &SSA,
  symbol_exprt &guard_ins, 
  var_listt &rb_vars,
  exprt::operandst &expr_vec)//put expressions like a=guard#ins? a#rb : a#init
{
  guard_ins=symbol_exprt("guard#ins",bool_typet());
  for(const exprt& var:SSA.params)
  {
    std::string var_name=
       id2string(to_symbol_expr(var).get_identifier());
    irep_idt name(var_name+"#rb"),name1(var_name+"#init");
    symbol_exprt var_rb(name,var.type()),var_init(name1,var.type());
    rb_vars.push_back(var_rb);
    ctx_renaming_map[var]=var_init;
    exprt rhs=if_exprt(guard_ins,var_rb,var_init);
    expr_vec.push_back(equal_exprt(var,rhs));
  }
}

void template_gen_rec_summaryt::create_comb_vars(const irep_idt &function_name,
  const local_SSAt &SSA,
  var_listt &comb_vars,
  exprt::operandst &expr_vec,//put expressions like a#comb=(g0 && dummy0)? a0 : (g1 && dummy1)? a1 : ..... a#nondet
  exprt &comb_guard,//comb_guard is like (g0 && dummy0) || .... (gK && dummyK)
  exprt::operandst &pre_guards)
{
  exprt::operandst guards_vec,comb_exprs;
  
  for(const symbol_exprt& var:SSA.params)
    get_comb_and_nondet_symb(var, comb_vars, comb_exprs);  
  for(const symbol_exprt& var:SSA.globals_in)
    get_comb_and_nondet_symb(var, comb_vars, comb_exprs);
  
  for(const local_SSAt::nodet &node:SSA.nodes)
  {
    for(const function_application_exprt &f_call:node.function_calls)
    {
      if(function_name==to_symbol_expr(f_call.function()).get_identifier()&&
          f_call.function().id()==ID_symbol)
      {
        exprt guard=SSA.guard_symbol(node.location);
        pre_guards.push_back(guard);
        replace_mapt r_map;
        if(options.get_bool_option("context-sensitive"))
        {
          symbol_exprt dummy_guard=get_dummy_guard(node.location->location_number);
          exprt cond=and_exprt(guard,dummy_guard);
          guards_vec.push_back(cond);
          std::vector<exprt>::iterator c_it=comb_exprs.begin();
          local_SSAt::var_listt::const_iterator p_it=SSA.params.begin();
          for(const exprt &arg:f_call.arguments())
          {
            exprt &expr=*c_it;
            expr=if_exprt(cond,arg,expr);//merging arguments
            r_map[*p_it]=arg;
            p_it++;
            c_it++;
          }
          
          local_SSAt::var_sett::iterator g_it=SSA.globals_in.begin();
          local_SSAt::var_sett globals_in;
          SSA.get_globals(node.location,globals_in,true,false);
          for(exprt g_in:globals_in)
          {
            exprt &expr=*c_it;
            expr=if_exprt(cond,g_in,expr);//merging global_ins
            r_map[*g_it]=g_in;
            g_it++;
            c_it++;
          }
        }
        local_SSAt::var_sett::iterator g_it=SSA.globals_out.begin();
        local_SSAt::var_sett globals_out;
        SSA.get_globals(node.location,globals_out,false);
        for(exprt g_out:globals_out)
        {
          r_map[*g_it]=g_out;
        }
        pre_renaming_maps.push_back(r_map);
      }
    }
  }

  unsigned size=SSA.params.size()+SSA.globals_in.size();
  for(unsigned i=0;i<size;i++)
  {
    expr_vec.push_back(equal_exprt(comb_vars.at(i),comb_exprs.at(i)));
  }
  comb_guard=disjunction(guards_vec);
}

void template_gen_rec_summaryt::collect_inout_vars(const irep_idt &function_name,
  const local_SSAt &SSA,
  exprt::operandst &pre_guards,
  bool forward)
{
  exprt::operandst expr_vec;
  symbol_exprt guard_ins;
  var_listt rb_vars,comb_vars;
  create_rb_vars(SSA, guard_ins, rb_vars, expr_vec);
  exprt comb_guard;//guard for comb variables
  
  create_comb_vars(function_name,
    SSA,
    comb_vars,
    expr_vec,
    comb_guard,
    pre_guards);
  
  // add params and globals_in in var_specs_no_out
  exprt first_guard=
    SSA.guard_symbol(SSA.goto_function.body.instructions.begin());
  add_vars(
    rb_vars,
    and_exprt(first_guard,guard_ins),
    comb_guard,
    forward ? domaint::ININD : domaint::OUTIND,
    var_specs_no_out);
  var_listt::const_iterator v_it=comb_vars.begin();
  for(domaint::var_spect var_spec:var_specs_no_out)
  {
    post_renaming_map[var_spec.var]=*v_it;
    v_it++;
  }
  
  // add params in var_specs
  add_vars(
    SSA.params,
    conjunction(pre_guards),
    first_guard,
    forward ? domaint::ININD : domaint::OUTIND,
    var_specs);
  // add globals_in in var_specs
  add_vars(
    SSA.globals_in,
    conjunction(pre_guards),
    first_guard,
    forward ? domaint::ININD : domaint::OUTIND,
    var_specs);
  // add globals_out(includes return values) in var_specs
  exprt last_guard=
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  add_vars(
    SSA.globals_out,
    conjunction(pre_guards),
    last_guard,
    forward ? domaint::OUTIND : domaint::ININD,
    var_specs); 
}
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
  exprt &ssa_addition,
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
      ssa_addition=collect_inout_vars(function_name, SSA, pre_guards, forward);
    else
    {
      ssa_addition=true_exprt();
      collect_variables_inout(SSA,forward);
    }
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
  for(const exprt& op:ssa_addition.operands())
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
    create_dep_map(SSA, node);
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
          if(get_args_dep(function_name, node, f_call)) 
            masking_guards.push_back(dummy_guard);
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

exprt template_gen_rec_summaryt::collect_inout_vars(const irep_idt &function_name,
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
    disjunction(pre_guards),
    first_guard,
    forward ? domaint::ININD : domaint::OUTIND,
    var_specs);
  // add globals_in in var_specs
  add_vars(
    SSA.globals_in,
    disjunction(pre_guards),
    first_guard,
    forward ? domaint::ININD : domaint::OUTIND,
    var_specs);
  // add globals_out(includes return values) in var_specs
  exprt last_guard=
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  add_vars(
    SSA.globals_out,
    disjunction(pre_guards),
    last_guard,
    forward ? domaint::OUTIND : domaint::ININD,
    var_specs);
  return conjunction(expr_vec);
}

void template_gen_rec_summaryt::instantiate_domains_for_rec(
  const local_SSAt &SSA,
  const exprt::operandst &pre_guards)
{
  replace_mapt &renaming_map=
    std_invariants ? aux_renaming_map : post_renaming_map;
  domain_ptr=
      new tpolyhedra_domaint(domain_number, renaming_map, SSA.ns);
  filter_template_domain();
  domain_ptr->set_pre_renaming_map(pre_renaming_maps);

  //IN templates(Octagon)  
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_interval_template(var_specs_no_out, SSA.ns, false);
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_sum_template(var_specs_no_out, SSA.ns, false);
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_difference_template(var_specs_no_out, SSA.ns, false);
  //OUT, LOOP templates
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_sum_template(var_specs, SSA.ns);
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_difference_template(var_specs, SSA.ns);
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_3_rel_template(var_specs, SSA.ns);
  /*static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_interval_template(var_specs, SSA.ns);*/
}

bool template_gen_rec_summaryt::get_dependency_for_rhs(
  exprt expr,
  local_SSAt::locationt loc)
{
  if(expr.id()==ID_symbol &&
     !(expr.is_constant()) && 
     !is_cond(expr) && 
     !is_guard(expr))
  {
    if(id2string(to_symbol_expr(expr).get_identifier()).
       find("#return_value#")!=std::string::npos)
    {
      return true;
    }
    irep_idt original_name=get_original_name(to_symbol_expr(expr));
    auto dep_ent=dep_maps.at(loc).find(original_name);
    assert(dep_ent!=dep_maps.at(loc).end());
    return dep_ent->second;
  }
  else
  {
    forall_operands(it, expr)
      if(get_dependency_for_rhs(*it, loc)) return true;
    return false;
  }
}

void template_gen_rec_summaryt::create_dep_map(
  const local_SSAt &SSA,
  const local_SSAt::nodet &cur_node)
{
  if(!options.get_bool_option("context-sensitive")) return;
  ssa_domaint::def_mapt cur_def_map=SSA.ssa_analysis[cur_node.location].def_map;
  rec_dep_mapt &cur_dep_map=dep_maps[cur_node.location];
  for(auto& def_ent:cur_def_map)
  {
    local_SSAt::locationt last_modified_loc=def_ent.second.source;
    if(id2string(def_ent.first).find("#return_value")!=std::string::npos)
      cur_dep_map.insert(std::make_pair(def_ent.first,true));//if it is return value
    else if(cur_node.location->location_number!=
       SSA.nodes.front().location->location_number &&//if current location is not 0
       last_modified_loc->location_number!=
       SSA.nodes.front().location->location_number &&
       last_modified_loc!=cur_node.location)//if last modified location is not 0
    {
      rec_dep_mapt prev_dep_map=dep_maps[last_modified_loc];
      rec_dep_mapt::iterator prev_dep_ent=prev_dep_map.find(def_ent.first);
      assert(prev_dep_ent!=prev_dep_map.end());
      cur_dep_map.insert(std::make_pair(
        def_ent.first, prev_dep_ent->second));//depends on previous
    }
    else
      cur_dep_map.insert(std::make_pair(def_ent.first,false));//no dependency
  }
  if(cur_node.location->location_number==
       SSA.nodes.front().location->location_number) return;
  for(equal_exprt eq:cur_node.equalities)
  {
    if(eq.rhs().id()==ID_symbol &&
       id2string(to_symbol_expr(eq.rhs()).get_identifier()).find("#arg")!=
       std::string::npos)
    {
      continue;
    }
    if(eq.lhs().id()==ID_symbol && 
       cur_dep_map.find(get_original_name(to_symbol_expr(eq.lhs())))!=cur_dep_map.end())
    {
      irep_idt lhs_name=
         get_original_name(to_symbol_expr(eq.lhs()));
      if(cur_def_map.find(lhs_name)!=cur_def_map.end())
      {
        cur_dep_map[lhs_name]=
          get_dependency_for_rhs(eq.rhs(),cur_node.location);//for all operands in rhs check dependency
      }
    }
  }
}

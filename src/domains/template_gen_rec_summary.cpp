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

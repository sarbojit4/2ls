/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   template_gen_rec_summary.h
 * Author: sarbojit
 *
 * Created on 19 March, 2018, 10:19 PM
 */

#ifndef TEMPLATE_GEN_REC_SUMMARY_H
#define TEMPLATE_GEN_REC_SUMMARY_H

#include "template_generator_summary.h"

class template_gen_rec_summaryt:public template_generator_summaryt {
public:
  typedef std::vector<std::pair<exprt,std::vector<exprt>>> tmpl_rename_mapt;
  explicit template_gen_rec_summaryt(
   optionst &_options,
   ssa_dbt &_ssa_db,
   ssa_local_unwindert &_ssa_local_unwinder):
   template_generator_summaryt(_options, _ssa_db, _ssa_local_unwinder)
  {
  }
  void operator()(const irep_idt &function_name,
    unsigned _domain_number,
    const local_SSAt &SSA,
    exprt &merge_exprt,
    bool forward=true);
    
  void create_comb_vars(const irep_idt &function_name,
    const local_SSAt &SSA,
    var_listt &comb_vars,
    exprt::operandst &expr_vec,//put expressions like a#comb=(g0 && dummy0)? a0 : (g1 && dummy1)? a1 : ..... a#nondet
    exprt &comb_guard,//comb_guard is like (g0 && dummy0) || .... (gK && dummyK)
    exprt::operandst &pre_guards);
    void create_rb_vars(const local_SSAt &SSA,
    symbol_exprt &guard_ins, 
    var_listt &rb_vars,
    exprt::operandst &expr_vec);//put expressions like a=guard#ins? a#rb : a#init
  exprt collect_inout_vars(const irep_idt &function_name,
    const local_SSAt &SSA,
    exprt::operandst &pre_guards,
    bool forward);
  void instantiate_domains_for_rec(const local_SSAt &SSA,
    const exprt::operandst &pre_guards);
  
  replace_mapt ctx_renaming_map;//used to rename calling context
  domaint::var_specst var_specs_no_out;//Exclude (OUT) variables
  std::vector<replace_mapt> pre_renaming_maps;
  typedef std::map<irep_idt, bool> rec_dep_mapt;
  typedef std::map<local_SSAt::locationt, rec_dep_mapt> dep_mapst;
  dep_mapst dep_maps;//for each variable, stores if it depends on some previous recursive call
  var_listt masking_guards;//used to discard some argument values if it depends on some earlier recursive call
  
  inline bool is_cond(const exprt &e)
  {
    return from_expr(e).find("$cond")!=std::string::npos;
  }
  inline bool is_guard(const exprt &e)
  {
    return from_expr(e).find("$guard")!=std::string::npos;
  }
  void create_dep_map(const local_SSAt &SSA, const local_SSAt::nodet &node);
  bool get_dependency_for_rhs(exprt expr, local_SSAt::locationt loc);
  bool get_args_dep(
    const irep_idt &function_name, 
    const local_SSAt::nodet node,
    const function_application_exprt f_call);
  
  inline symbol_exprt get_dummy_guard(unsigned loc)
  {
    return symbol_exprt(dstring("dummy#"+std::to_string(loc)),bool_typet());
  }
  inline void get_comb_and_nondet_symb(const symbol_exprt &var,
    var_listt &comb_vars,
    exprt::operandst &comb_exprs)
  {
    std::string var_name=id2string(var.get_identifier());
    comb_vars.push_back(symbol_exprt(dstring(var_name+"#comb"),var.type()));
    comb_exprs.push_back(symbol_exprt(dstring(var_name+"#nondet"),var.type()));  
  }
};

#endif /* TEMPLATE_GEN_REC_SUMMARY_H */


/*******************************************************************\

Module: Indexing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/message.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_model.h>

#include "index.h"
#include "html_report.h"
#include "get_function.h"
#include "one_program_check.h"
#include "ssa_data_flow.h"

/*******************************************************************\

Function: one_program_check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check_function(
  const irep_idt &id,
  const goto_functionst::goto_functiont &f,
  const namespacet &ns,
  std::ostream &report,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  message.status() << "Data-flow fixed-point" << messaget::eom;

  // build SSA
  function_SSAt function_SSA(f, ns);
  
  // now do fixed-point
  ssa_data_flowt ssa_data_flow(function_SSA);
  
  // now give to SAT
}

/*******************************************************************\

Function: one_program_check_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check_function(
  const indext &index,
  const std::string &function,
  std::ostream &report,
  message_handlert &message_handler)
{
  const irep_idt id="c::"+function;

  get_functiont get_function(index);
  get_function.set_message_handler(message_handler);
  
  const namespacet &ns=get_function.ns;
  
  messaget message(message_handler);
  
  const goto_functionst::goto_functiont *index_fkt=
    get_function(id);
  
  if(index_fkt==NULL)
  {
    message.error() << "function \"" << function
                    << "\" not found in index" << messaget::eom;
    return;
  }

  one_program_check_function(id, *index_fkt, ns, report, message_handler);
}

/*******************************************************************\

Function: one_program_check_all

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check_all(
  const indext &index,
  std::ostream &report,
  message_handlert &message_handler)
{
  // we do this by file in the index
  
  messaget message(message_handler);

  for(indext::file_to_functiont::const_iterator
      file_it=index.file_to_function.begin();
      file_it!=index.file_to_function.end();
      file_it++)
  {
    message.status() << "Processing \"" << file_it->first << "\""
                     << messaget::eom;
    
    // read the file
    goto_modelt model;
    read_goto_binary(id2string(file_it->first), model, message_handler);
   
    const namespacet ns(model.symbol_table); 
    const std::set<irep_idt> &functions=file_it->second;

    // now do all functions from model
    for(std::set<irep_idt>::const_iterator
        fkt_it=functions.begin();
        fkt_it!=functions.end();
        fkt_it++)
    {
      const irep_idt &id=*fkt_it;
      const goto_functionst::goto_functiont *index_fkt=
        &model.goto_functions.function_map.find(id)->second;
    
      message.status("Checking \""+id2string(id)+"\"");
      
      report << "<h2>Function " << id << " in " << file_it->first
             << "</h2>" << std::endl;
      
      one_program_check_function(id, *index_fkt, ns, report, message_handler);
    }
  }
}

/*******************************************************************\

Function: one_program_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void one_program_check(
  const indext &index,
  const std::string &function,
  message_handlert &message_handler)
{
  std::string report_file_name="deltacheck.html";
  std::ofstream out(report_file_name.c_str());

  if(!out)
  {
    messaget message(message_handler);
    message.error() << "failed to write to \""
                    << report_file_name << "\"" << messaget::eom;
    return;
  }

  html_report_header(out, index);

  if(function=="")
    one_program_check_all(index, out, message_handler);
  else
    one_program_check_function(index, function, out, message_handler);

  html_report_footer(out, index);
}

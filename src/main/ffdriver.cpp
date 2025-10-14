#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <iostream>
#include <fstream>

int main(int argc, char *argv[]) {
  std::string file = argv[1];
  cvc5::TermManager tm; 
  cvc5::Solver slv(tm); 
  cvc5::parser::InputParser parser(&slv);
  cvc5::parser::SymbolManager* sm = parser.getSymbolManager();
  cvc5::parser::Command cmd;
  
  slv.setOption("ff-certificate", "true");

  parser.setFileInput(cvc5::modes::InputLanguage::SMT_LIB_2_6, file);
  while (true) {
    cmd = parser.nextCommand(); 
    if (cmd.isNull()) { break; }
    cmd.invoke(&slv, sm, std::cout);
  }

  cvc5::Result r = slv.checkSatFF(sm->getNamedTerms());
}
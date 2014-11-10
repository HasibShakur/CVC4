#include "cvc4_public.h"

#ifndef __CVC4__PARSER_COEFFICIENTCONTAINER_H
#define __CVC4__PARSER_COEFFICIENTCONTAINER_H

#include<iostream>
#include "expr/node.h"

namespace CVC4{
class CVC4_PUBLIC CoefficientContainer
{
private:
  static int id ;
  static Node var;
  static Node coefficient;
public:
  CoefficientContainer(Node v,Node c)
  {
    var = v;
    coefficient = c;
    id = id +1;
  }
  static Node getVar();
  static Node getCoefficient();
};
}

#endif

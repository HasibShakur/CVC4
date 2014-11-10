#include<iostream>
#include<expr/node.h>
#include<expr/CoefficientContainer.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;

Node CoefficientContainer::getVar()
{
  return var;
}
Node CoefficientContainer::getCoefficient()
{
  return coefficient;
}

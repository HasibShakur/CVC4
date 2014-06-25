#include<iostream>
#include "expr/node.h"
#include "expr/expr_template.h"
#include "parser/QuantifierEliminate.h"
#include "parser/input.h"
#include "parser/parser.h"
using namespace std;
using namespace CVC4;
using namespace CVC4::kind;

QuantifierEliminate::QuantifierEliminate(const CVC4::Expr& ex)
{
  this->expression = ex;
}
QuantifierEliminate::~QuantifierEliminate(){}
CVC4::Expr QuantifierEliminate::getExpression()
{
  return this->expression;
}




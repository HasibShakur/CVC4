#include<iostream>
#include<vector>
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
QuantifierEliminate::void parseQuantifiers(const CVC4::Expr& ex)
{
  Node tempBody = Node::fromExpr(ex);
  for(size_t i= 0;i<tempBody[0].getNumChildren();i++)
  {
    if(tempBody[0][i].getKind() == kind::FORALL || tempBody[0][i].getKind() == kind::EXISTS )
    {
      d_quants.push_back(tempBody[0][i].getType());
    }
  }
}
QuantifierEliminate::int getNumQuantifiers()
{
  return (int)d_quants.size();
}
QuantifierEliminate::Node getQuantifier( int i )
{
  return this->d_quants[i];
}




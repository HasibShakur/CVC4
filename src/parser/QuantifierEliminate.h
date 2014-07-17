#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"

//using namespace CVC4;
namespace CVC4{
 namespace parser{
  namespace QuantifierEliminate{

//attribute for "contains instantiation constants from"
struct NestedQuantAttributeId {};
typedef expr::Attribute<NestedQuantAttributeId, Node> NestedQuantAttribute;

class QuantifierEliminate {
private:
  CVC4::Expr expression;
  Node computePrenex(Node body,std::vector< Node >& args, bool pol);
  void setNestedQuantifiers( Node n, Node q );
  void setNestedQuantifiers2( Node n, Node q, std::vector< Node >& processed );
  Node computeNNF(Node body);
  //Node normalizeBody(Node body);
  //Node replaceUniversal(Node body);
public:
  QuantifierEliminate(const CVC4::Expr& ex);
  ~QuantifierEliminate();
  CVC4::Expr getExpression();
  void setExpression(const CVC4::Expr& ex);
  /*void parseQuantifiers(const CVC4::Expr& ex);
  * get number of quantifiers
  int getNumQuantifiers();
  * get quantifier
  Node getQuantifier(int i);
  void receiveBoundVariables(const CVC4::Expr& ex);
  void receiveFreeVariables(const CVC4::Expr& ex);*/
  CVC4::Expr getPrenexExpression(const CVC4::Expr& ex);
  CVC4::Expr simplifyExpression(const CVC4::Expr& ex);
};
  }
 }
}

#endif

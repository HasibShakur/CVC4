#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "theory/rewriter.h"

namespace CVC4{
//namespace parser{
//namespace QuantifierEliminate{

//attribute for "contains instantiation constants from"
//struct NestedQuantAttributeId {};
//typedef expr::Attribute<NestedQuantAttributeId, Node> NestedQuantAttribute;

class QuantifierEliminate {
private:
  Expr expression;
  Node convertToPrenex(Node body,std::vector< Node >& args, bool pol);
 // void setNestedQuantifiers( Node n, Node q );
 // void setNestedQuantifiers2( Node n, Node q, std::vector< Node >& processed );
  Node convertToNNF(Node body);
  bool isLiteral(Node n);
  //Node normalizeBody(Node body);
  //Node replaceUniversal(Node body);
public:
  QuantifierEliminate(const Expr& ex);
  ~QuantifierEliminate();
  Expr getExpression();
  void setExpression(const Expr& ex);
  /*void parseQuantifiers(const CVC4::Expr& ex);
  * get number of quantifiers
  int getNumQuantifiers();
  * get quantifier
  Node getQuantifier(int i);
  void receiveBoundVariables(const CVC4::Expr& ex);
  void receiveFreeVariables(const CVC4::Expr& ex);*/
  Node getPrenexExpression(const Expr& e);
  Node simplifyExpression(const Expr& e);
};
}
//}
//}

#endif

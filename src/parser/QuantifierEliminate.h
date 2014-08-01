#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "theory/rewriter.h"

namespace CVC4{
namespace smt{
//namespace qe{

//attribute for "contains instantiation constants from"
//struct QeNestedQuantAttributeId {};
//typedef expr::Attribute<QeNestedQuantAttributeId, Node> QeNestedQuantAttribute;

class QuantifierEliminate {
private:
  CVC4::Expr expression;
  Node convertToPrenex(Node body,std::vector< Node >& args, bool pol);
  //void setNestedQuantifiers( Node n, Node q );
  //void setNestedQuantifiers2( Node n, Node q, std::vector< Node >& processed );
  Node convertToNNF(Node body);
  bool isLiteral(Node n);
public:
  QuantifierEliminate();
  ~QuantifierEliminate();
  CVC4::Expr getExpression();
  void setExpression(const Expr& e);
  Node getPrenexExpression(const Expr& e);
  Node simplifyExpression(const Expr& e);
};
}
}
//}
//}

#endif

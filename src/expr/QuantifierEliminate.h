#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"

namespace CVC4{
class CVC4_PUBLIC QuantifierEliminate {
private:
   //CVC4::Node normalizeBody(CVC4::Node body);
  /*static Node convertToNNF(Node body);
  static bool isLiteral(Node n);*/
  //static Node convertToPrenex(Node body, std::vector< Node >& args, bool pol);
  //static Node convertExistentialToForAll(Node f);
public:
//  static Node simplifyExpression(Node n);
  static bool isLiteralQE(Node n);
  static bool isCubeQE( Node n );
  static bool isClauseQE( Node n );
  static void addNodeToOrBuilderQE( Node n, NodeBuilder<>& t );
  static Node computeClauseQE( Node n );
  static void computeArgsQE( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n );
  static void computeArgVecQE( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
  static Node computeCNFQE( Node body, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred );
  static Node getPrenexExpressionQE(Node n);
  static Node convertToPrenexQE(Node body, std::vector< Node >& args, bool pol);
  static Node convertExistentialToForAllQE(Node f);
};
}
#endif

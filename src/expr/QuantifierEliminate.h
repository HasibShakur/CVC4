#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"

namespace CVC4{
class CVC4_PUBLIC QuantifierEliminate {
private:
  /*static Node getPrenexExpressionQE(Node n);
  static Node convertToPrenexQE(Node body, std::vector< Node >& args, bool pol);
  static Node convertExistentialToForAllQE(Node f);*/
    static bool isClauseQE( Node n );
    static bool isLiteralQE( Node n );
    static bool isCubeQE( Node n );
    static void addNodeToOrBuilderQE( Node n, NodeBuilder<>& t );
    static Node mkForAllQE( std::vector< Node >& args, Node body, Node ipl );
    static void computeArgsQE( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n );
    static void computeArgVecQE( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
    static bool hasArgQE( std::vector< Node >& args, Node n );
    static void setNestedQuantifiersQE( Node n, Node q );
    static void setNestedQuantifiers2QE( Node n, Node q, std::vector< Node >& processed );
    static Node computeClauseQE( Node n );
    static Node computeCNFQE( Node body, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred );
    static bool isRewriteRuleQE (Node n);
    static Node getRewriteRuleQE (Node n);
    static bool doOperationQE(Node f, bool isNested, int cnfOperation);
    static Node computeOperationQE( Node f, bool isNested, int cnfOperation );
public:
    static void convertNodeToCNF(Node n);


};
}
#endif

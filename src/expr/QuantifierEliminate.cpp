//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "expr/QuantifierEliminate.h"
#include "expr/attribute.h"
#include "printer/smt2/smt2_printer.h"
#include "util/output.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::printer;

struct QENestedQuantAttributeId {};
typedef expr::Attribute<QENestedQuantAttributeId, Node> QuantAttrib;

bool QuantifierEliminate::isLiteralQE( Node n ){
  switch( n.getKind() ){
  case kind::NOT:
    return isLiteralQE( n[0] );
    break;
  case kind::OR:
  case kind::AND:
  case kind::IMPLIES:
  case kind::XOR:
  case kind::ITE:
  case kind::IFF:
    return false;
    break;
  default:
    break;
  }
  return true;
}
bool QuantifierEliminate::isRelationalOperatorTypeQE(Kind k)
{
  switch( k )
  {
    case kind::LT:
    case kind::GT:
    case kind::LEQ:
    case kind::GEQ:
    case kind::EQUAL:
      return true;
    default:
      return false;
  }
}

Node QuantifierEliminate::convertToPrenexQE(Node body, std::vector< Node >& args, bool pol)
{
  if( body.getKind()== kind::FORALL ){
      if( pol ){
        std::vector< Node > terms;
        std::vector< Node > subs;
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          //if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ){
          terms.push_back( body[0][i] );
          subs.push_back( NodeManager::currentNM()->mkBoundVar( body[0][i].getType() ) );
        }
        args.insert( args.end(), subs.begin(), subs.end() );
        Node newBody = body[1];
        newBody = newBody.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
        if(newBody.isNull())
        {
          Debug("expr-qe") << "newBody is null in convertToPrenex" << "\n" ;
        }
      //  Debug("expr-qe") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << "\n";
        return newBody;
      }else{
        return body;
      }
    }else if( body.getKind()== kind::ITE || body.getKind()== kind::XOR || body.getKind()== kind::IFF ){
      return body;
    }else{
      Assert( body.getKind()!= kind::EXISTS );
      bool childrenChanged = false;
      std::vector< Node > newChildren;
      for( int i=0; i<(int)body.getNumChildren(); i++ ){
        bool newPol = body.getKind()== kind::NOT  ? !pol : pol;
        Node n = convertToPrenexQE( body[i], args, newPol );
        newChildren.push_back( n );
        if( n!=body[i] ){
          childrenChanged = true;
        }
      }
      if( childrenChanged ){
        if( body.getKind()==NOT && newChildren[0].getKind()== kind::NOT ){
          return newChildren[0][0];
        }else{
          return NodeManager::currentNM()->mkNode( body.getKind(), newChildren );
        }
      }else{
        return body;
      }
    }
}
/*Node QuantifierEliminate::convertToNNFQE(Node body)
{
  if( body.getKind()== kind::NOT ){
    if( body[0].getKind()== kind::NOT ){
      Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][0].getKind() << "\n";
      return convertToNNFQE( body[0][0] );
    }else if( isLiteralQE( body[0] ) ){
      Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getKind() << "\n";
      return body;
    }else{
      std::vector< CVC4::Node > children;
      Kind k = body[0].getKind();
      Debug("expr-qetest") << "Inside NNF convertion of the formula kind (as per the given input it should be and) "<< k << "\n";
      if( body[0].getKind()== kind::OR || body[0].getKind()== kind::AND ){
        Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getNumChildren() << "\n";
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][i].getKind() << "\n";
          children.push_back( convertToNNFQE( body[0][i].notNode() ) );
        }
        Debug("expr-qetest") << "Size of children here "<< children.size() << "\n";
        k = body[0].getKind()== kind::AND ? kind::OR : kind::AND;
      }else if( body[0].getKind()== kind::IFF ){
        for( int i=0; i<2; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( convertToNNFQE( nn ) );
        }
      }else if( body[0].getKind()== kind::ITE ){
        for( int i=0; i<3; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( convertToNNFQE( nn ) );
        }
      }else{
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return NodeManager::currentNM()->mkNode( k, children );
    }
  }else if( isLiteralQE( body ) ){
    return body;
  }else{
    std::vector< CVC4::Node > children;
    bool childrenChanged = false;
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      Node nc = convertToNNFQE( body[i] );
      children.push_back( nc );
      childrenChanged = childrenChanged || nc!=body[i];
    }
    if( childrenChanged ){
      return NodeManager::currentNM()->mkNode( body.getKind(), children );
    }else{
      return body;
    }
  }
}*/
Node QuantifierEliminate::convertToNNFQE(Node body, NodeManager* currNM)
{

  if( body.getKind()== kind::NOT ){
      if( body[0].getKind()== kind::NOT ){
        Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][0].getKind() << "\n";
        return convertToNNFQE( body[0][0],currNM );
      }else if( isLiteralQE( body[0] ) ){
        Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getKind() << "\n";
        return body;
      }
      else
      {
        std::vector< CVC4::Node > children;
        Kind k = body[0].getKind();
        Debug("expr-qetest") << "Inside NNF convertion of the formula kind (as per the given input it should be and) "<< k << "\n";
        if( body[0].getKind()== kind::OR || body[0].getKind()== kind::AND ){
          Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0].getNumChildren() << "\n";
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            Debug("expr-qetest") << "Inside NNF convertion of the formula "<< body[0][i].getKind() << "\n";
            if(isRelationalOperatorTypeQE(body[0][i].getKind()))
            {
               if(body[0][i].getKind() == kind::GEQ)
               {
                 Debug("expr-qetest") << "Debug reaches here before the creation of node and the number of children is "<< body[0][i].getNumChildren() << "\n";
                 std::vector< CVC4::Node > children_relation;
                 for(int j = 0; j< (int)body[0][i].getNumChildren();j++)
                 {
                   if(!body[0][i][j].isNull())
                   {
                     Debug("expr-qetest")<<"inner_children element " << j <<" is not null\n";
                     Debug("expr-qetest")<<"Kind of inner children element "<<body[0][i][j].getKind()<<"\n";
                     TypeNode tn = body[0][i][j].getType(true);
                     Debug("expr-qetest")<<"Type of each element "<<tn.getKind()<<"\n";
                     children_relation.push_back( body[0][i][j] );
                     Debug("expr-qetest")<<"added successfully to inner_children\n";
                   }
                 }

                 Debug("expr-qetest") << "Inner children size "<<children_relation.size() << "\n";
                 Node lt = currNM->mkNode(kind::LT,children_relation[0],children_relation[1]);
                 Debug("expr-qetest") << "After negation of the GEQ the kind will be lt "<< body[0][i].getKind() << "\n";
                 children.push_back( lt );
               }
               // to do code
            }
            //children.push_back( convertToNNFQE( body[0][i].notNode() ) );
         }
          Debug("expr-qetest")<<"Size of children is "<<children.size()<<"\n";
          k = body[0].getKind()== kind::AND ? kind::OR : kind::AND;
          Debug("expr-qetest")<<"New kind after negation "<<k<<"\n";
      }
      else{
            Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
            return body;
          }
        return currNM->mkNode( k, children );
     }
  }
  else if( isLiteralQE( body ) ){
      return body;
    }else{
      std::vector< CVC4::Node > children;
      bool childrenChanged = false;
      for( int i=0; i<(int)body.getNumChildren(); i++ ){
        Node nc = convertToNNFQE( body[i],currNM );
        children.push_back( nc );
        childrenChanged = childrenChanged || nc!=body[i];
      }
      if( childrenChanged ){
        return currNM->mkNode( body.getKind(), children );
      }else{
        return body;
      }
    }
}

Node QuantifierEliminate::doPreprocessing(Expr ex)
{
  Node temp_in = NodeTemplate<true>(ex);
  Debug("expr-qetest") << "------- Inside doProcessing Method ------" << "\n";
  Node in;
  if(temp_in.getKind() == kind::NOT)
  {
    in = temp_in[0];
    Debug("expr-qetest") << in.getKind() << "\n";
    Debug("expr-qetest") << in.getNumChildren() << "\n";
  }
  else
  {
    in  = temp_in;
    Debug("expr-qetest") << in.getKind() << "\n";
    Debug("expr-qetest") << in.getNumChildren() << "\n";
  }
  if( in.getKind()== kind::FORALL ){
      std::vector< Node > args;
      for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
        args.push_back( in[0][i] );
    }
    NodeBuilder<> defs(kind::AND);
    Node n = in[1];
    Node ipl;
    Debug("expr-qetest") << "kind of n "<<n.getKind() << "\n";
    Debug("expr-qetest") << "number of children  of n "<<n.getNumChildren() << "\n";
    if( in.getNumChildren()==3 ){
      ipl = in[2];
    }
    if(n.isNull())
    {
      Debug("expr-qetest") << "Node n is null in doPreprocessing after Node n = in[1]" << "\n";
    }
    n = convertToPrenexQE(n,args, true);
    Debug("expr-qetest") << "kind of after prenexing "<<n.getKind() << "\n";
    Debug("expr-qetest") << "number of children  of n after prenexing "<<n.getNumChildren() << "\n";
    if(n.isNull())
    {
      Debug("expr-qetest") << "Node n is null in doPreprocessing after Node n = convertToPrenexQE(n,args, true)" << "\n";
    }
    NodeManager* currNM = NodeManager::currentNM();
    Node rewrittenNode = convertToNNFQE(n,currNM);
   // n = convertToNNFQE(n);
    Debug("expr-qetest") << "kind of after rewriting "<<rewrittenNode.getKind() << "\n";
    Debug("expr-qetest") << "number of children  of n after rewriting "<<rewrittenNode.getNumChildren() << "\n";
    if(rewrittenNode.isNull())
    {
      Debug("expr-qetest") << "Node rewrittenNode is null in doPreprocessing after rewriting " << "\n";
    }
    if(in[1] == rewrittenNode && args.size() == in[0].getNumChildren())
    {
       return in;
    }
    else
    {
      if(args.empty())
      {
        defs << rewrittenNode;
      }
      else
      {
        std::vector< Node > children;
        children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
        children.push_back( rewrittenNode );
        if( !ipl.isNull() ){
           children.push_back( ipl );
        }
        defs << NodeManager::currentNM()->mkNode(kind::FORALL, children );
      }
      return defs.getNumChildren()==1 ? defs.getChild( 0 ) : defs.constructNode();
    }
  }
  else
  {
    return in;
  }
}




/*CVC4::Node QuantifierEliminate::normalizeBody(CVC4::Node body)
{
  bool rewritten = false;
  Node normalized;
  for(int i=0;i<(int)body.getNumChildren();i++)
  {
    if(body[i].getKind() == NOT)
    {
      //If it is not then do the normalization of the expression whose kind is not
      //Just call the negateNode on the simplification done on the else part
    }
    else
    {
      // If it is not of the kind not then directly normalize this
      if(this->isLiteral(body[i]))
      {
        // If it is a literal then we need to do nothing
        rewritten = false;
      }
      else if(body[i].getKind()==EQUAL)
      {
      //  body[i].kinded_iterator::begin(body[i],EQUAL);
      }
      // If the operator is > then convert it to < by just exchanging the operators then making a node using mkNode
      // If the operator is = then use the following conversion s=t <==> s>t+1 and t>s+1
    }
  }
  if(!rewritten)
  {
    return body;
  }
  else
  {
    return normalized;
  }
}*/
/*Node QuantifierEliminate::simplifyExpression(Node n)
{
  // 1st phase of simplification is converting the expression to NNF
  Node nnfNode = convertToNNF(n);
  // 3rd phase of simplification is applying the replace rules
  //Node normalizedBody = normalizeBody(nnfNode);
  // 4th phase of simplification is
  return nnfNode;
}*/
/*bool QuantifierEliminate::isClauseQE( Node n ){
  if( isLiteralQE( n ) ){
    return true;
  }else if( n.getKind()==kind::NOT ){
    return isCubeQE( n[0] );
  }else if( n.getKind()==kind::OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isClauseQE( n[i] ) ){
        return false;
      }
    }
    return true;
  }else if( n.getKind()==kind::IMPLIES ){
    return isCubeQE( n[0] ) && isClauseQE( n[1] );
  }else{
    return false;
  }
}*/





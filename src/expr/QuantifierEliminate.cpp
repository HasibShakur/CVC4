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
  case kind::EQUAL:
    return n[0].getType()!=NodeManager::currentNM()->booleanType();
    break;
  case kind::GEQ:
    return n[0].getType()!=NodeManager::currentNM()->integerType();
  case kind::LEQ:
    return n[0].getType()!=NodeManager::currentNM()->integerType();
  default:
    break;
  }
  return true;
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
Node QuantifierEliminate::convertToNNFQE(Node body)
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
}
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
}


bool QuantifierEliminate::isCubeQE( Node n ){
  if( isLiteralQE( n ) ){
    return true;
  }else if( n.getKind()==kind::NOT ){
    return isClauseQE( n[0] );
  }else if( n.getKind()==kind::AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isCubeQE( n[i] ) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void QuantifierEliminate::addNodeToOrBuilderQE( Node n, NodeBuilder<>& t ){
  if( n.getKind()==kind::OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      t << n[i];
    }
  }else{
    t << n;
  }
}

Node QuantifierEliminate::mkForAllQE( std::vector< Node >& args, Node body, Node ipl ){
  std::vector< Node > activeArgs;
  computeArgVecQE( args, activeArgs, body );
  if( activeArgs.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, activeArgs ) );
    children.push_back( body );
    if( !ipl.isNull() ){
      children.push_back( ipl );
    }
    return NodeManager::currentNM()->mkNode( kind::FORALL, children );
  }
}

void QuantifierEliminate::computeArgsQE( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n ){
  if( n.getKind()==kind::BOUND_VARIABLE ){
    if( std::find( args.begin(), args.end(), n )!=args.end() ){
      activeMap[ n ] = true;
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeArgsQE( args, activeMap, n[i] );
    }
  }
}

void QuantifierEliminate::computeArgVecQE( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n ) {
  std::map< Node, bool > activeMap;
  computeArgsQE( args, activeMap, n );
  for( unsigned i=0; i<args.size(); i++ ){
    if( activeMap[args[i]] ){
      activeArgs.push_back( args[i] );
    }
  }
}


bool QuantifierEliminate::hasArgQE( std::vector< Node >& args, Node n ){
  if( std::find( args.begin(), args.end(), n )!=args.end() ){
    return true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( hasArgQE( args, n[i] ) ){
        return true;
      }
    }
    return false;
  }
}

void QuantifierEliminate::setNestedQuantifiersQE( Node n, Node q ){
  std::vector< Node > processed;
  setNestedQuantifiers2QE( n, q, processed );
}

void QuantifierEliminate::setNestedQuantifiers2QE( Node n, Node q, std::vector< Node >& processed ) {
  if( std::find( processed.begin(), processed.end(), n )==processed.end() ){
    processed.push_back( n );
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      Trace("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
      QuantAttrib qa;
      n[0].setAttribute(qa,q);
    }
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      setNestedQuantifiers2QE( n[i], q, processed );
    }
  }
}

Node QuantifierEliminate::computeClauseQE( Node n ){
  Assert( isClauseQE( n ) );
  if( isLiteralQE( n ) ){
    return n;
  }else{
    NodeBuilder<> t(OR);
    if( n.getKind()==kind::NOT ){
      if( n[0].getKind()== kind::NOT ){
        return computeClauseQE( n[0][0] );
      }else{
        //De-Morgan's law
        Assert( n[0].getKind()== kind::AND );
        for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
          Node nn = computeClauseQE( n[0][i].notNode() );
          addNodeToOrBuilderQE( nn, t );
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        Node nn = computeClauseQE( n[i] );
        addNodeToOrBuilderQE( nn, t );
      }
    }
    return t.constructNode();
  }
}
Node QuantifierEliminate::computeCNFQE( Node n, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred ){
  if( isLiteralQE( n ) ){
    return n;
  }else if( !forcePred && isClauseQE( n ) ){
    return computeClauseQE( n );
  }else{
    Kind k = n.getKind();
    NodeBuilder<> t(k);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node nc = n[i];
      Node ncnf = computeCNFQE( nc, args, defs, k!= kind::OR );
      if( k== kind::OR ){
        addNodeToOrBuilderQE( ncnf, t );
      }else{
        t << ncnf;
      }
    }
    if( !forcePred && k== kind::OR ){
      return t.constructNode();
    }else{
      //compute the free variables
      Node nt = t;
      std::vector< Node > activeArgs;
      computeArgVecQE( args, activeArgs, nt );
      std::vector< TypeNode > argTypes;
      for( int i=0; i<(int)activeArgs.size(); i++ ){
        argTypes.push_back( activeArgs[i].getType() );
      }
      //create the predicate
      Assert( argTypes.size()>0 );
      TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, NodeManager::currentNM()->booleanType() );
      std::stringstream ss;
      ss << "cnf_" << n.getKind() << "_" << n.getId();
      Node op = NodeManager::currentNM()->mkSkolem( ss.str(), typ, "was created by the quantifiers rewriter" );
      std::vector< Node > predArgs;
      predArgs.push_back( op );
      predArgs.insert( predArgs.end(), activeArgs.begin(), activeArgs.end() );
      Node pred = NodeManager::currentNM()->mkNode( APPLY_UF, predArgs );
      Trace("quantifiers-rewrite-cnf-debug") << "Made predicate " << pred << " for " << nt << std::endl;
      //create the bound var list
      Node bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, activeArgs );
      //now, look at the structure of nt
      if( nt.getKind()== kind::NOT ){
        //case for NOT
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[0].notNode() : nt[0] );
          tt << ( i==0 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()== kind::OR ){
        //case for OR
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i].notNode() << pred;
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i];
        }
        tt << pred.notNode();
        defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()== kind::AND ){
        //case for AND
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i] << pred.notNode();
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i].notNode();
        }
        tt << pred;
        defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()== kind::IFF ){
        //case for IFF
        for( int i=0; i<4; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( ( i==0 || i==3 ) ? nt[0].notNode() : nt[0] );
          tt << ( ( i==1 || i==3 ) ? nt[1].notNode() : nt[1] );
          tt << ( ( i==0 || i==1 ) ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()== kind::ITE ){
        //case for ITE
        for( int j=1; j<=2; j++ ){
          for( int i=0; i<2; i++ ){
            NodeBuilder<> tt(OR);
            tt << ( ( j==1 ) ? nt[0].notNode() : nt[0] );
            tt << ( ( i==1 ) ? nt[j].notNode() : nt[j] );
            tt << ( ( i==0 ) ? pred.notNode() : pred );
            defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
          }
        }
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[1].notNode() : nt[1] );
          tt << ( i==0 ? nt[2].notNode() : nt[2] );
          tt << ( i==1 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
      }else{
        Notice() << "Unhandled Quantifiers CNF: " << nt << std::endl;
      }
      return pred;
    }
  }
}*/
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
    n = convertToNNFQE(n);
    Debug("expr-qetest") << "kind of after nnf "<<n.getKind() << "\n";
    Debug("expr-qetest") << "number of children  of n after nnf "<<n.getNumChildren() << "\n";
    if(n.isNull())
    {
      Debug("expr-qetest") << "Node n is null in doPreprocessing after Node n = convertToNNFQE(n)" << "\n";
    }
    if(in[1] == n && args.size() == in[0].getNumChildren())
    {
       return in;
    }
    else
    {
      if(args.empty())
      {
        defs << n;
      }
      else
      {
        std::vector< Node > children;
        children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
        children.push_back( n );
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
}



bool QuantifierEliminate::isCubeQE( Node n ){
  if( isLiteralQE( n ) ){
    return true;
  }else if( n.getKind()==kind::NOT ){
    return isClauseQE( n[0] );
  }else if( n.getKind()==kind::AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isCubeQE( n[i] ) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void QuantifierEliminate::addNodeToOrBuilderQE( Node n, NodeBuilder<>& t ){
  if( n.getKind()==kind::OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      t << n[i];
    }
  }else{
    t << n;
  }
}

Node QuantifierEliminate::mkForAllQE( std::vector< Node >& args, Node body, Node ipl ){
  std::vector< Node > activeArgs;
  computeArgVecQE( args, activeArgs, body );
  if( activeArgs.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, activeArgs ) );
    children.push_back( body );
    if( !ipl.isNull() ){
      children.push_back( ipl );
    }
    return NodeManager::currentNM()->mkNode( kind::FORALL, children );
  }
}

void QuantifierEliminate::computeArgsQE( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n ){
  if( n.getKind()==kind::BOUND_VARIABLE ){
    if( std::find( args.begin(), args.end(), n )!=args.end() ){
      activeMap[ n ] = true;
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeArgsQE( args, activeMap, n[i] );
    }
  }
}

void QuantifierEliminate::computeArgVecQE( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n ) {
  std::map< Node, bool > activeMap;
  computeArgsQE( args, activeMap, n );
  for( unsigned i=0; i<args.size(); i++ ){
    if( activeMap[args[i]] ){
      activeArgs.push_back( args[i] );
    }
  }
}


bool QuantifierEliminate::hasArgQE( std::vector< Node >& args, Node n ){
  if( std::find( args.begin(), args.end(), n )!=args.end() ){
    return true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( hasArgQE( args, n[i] ) ){
        return true;
      }
    }
    return false;
  }
}

void QuantifierEliminate::setNestedQuantifiersQE( Node n, Node q ){
  std::vector< Node > processed;
  setNestedQuantifiers2QE( n, q, processed );
}

void QuantifierEliminate::setNestedQuantifiers2QE( Node n, Node q, std::vector< Node >& processed ) {
  if( std::find( processed.begin(), processed.end(), n )==processed.end() ){
    processed.push_back( n );
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      Trace("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
      QuantAttrib qa;
      n[0].setAttribute(qa,q);
    }
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      setNestedQuantifiers2QE( n[i], q, processed );
    }
  }
}

Node QuantifierEliminate::computeClauseQE( Node n ){
  Assert( isClauseQE( n ) );
  if( isLiteralQE( n ) ){
    return n;
  }else{
    NodeBuilder<> t(OR);
    if( n.getKind()==kind::NOT ){
      if( n[0].getKind()== kind::NOT ){
        return computeClauseQE( n[0][0] );
      }else{
        //De-Morgan's law
        Assert( n[0].getKind()== kind::AND );
        for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
          Node nn = computeClauseQE( n[0][i].notNode() );
          addNodeToOrBuilderQE( nn, t );
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        Node nn = computeClauseQE( n[i] );
        addNodeToOrBuilderQE( nn, t );
      }
    }
    return t.constructNode();
  }
}

Node QuantifierEliminate::computeCNFQE( Node n, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred ){
  if( isLiteralQE( n ) ){
    return n;
  }else if( !forcePred && isClauseQE( n ) ){
    return computeClauseQE( n );
  }else{
    Kind k = n.getKind();
    NodeBuilder<> t(k);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node nc = n[i];
      Node ncnf = computeCNFQE( nc, args, defs, k!= kind::OR );
      if( k== kind::OR ){
        addNodeToOrBuilderQE( ncnf, t );
      }else{
        t << ncnf;
      }
    }
    if( !forcePred && k== kind::OR ){
      return t.constructNode();
    }else{
      //compute the free variables
      Node nt = t;
      std::vector< Node > activeArgs;
      computeArgVecQE( args, activeArgs, nt );
      std::vector< TypeNode > argTypes;
      for( int i=0; i<(int)activeArgs.size(); i++ ){
        argTypes.push_back( activeArgs[i].getType() );
      }
      //create the predicate
      Assert( argTypes.size()>0 );
      TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, NodeManager::currentNM()->booleanType() );
      std::stringstream ss;
      ss << "cnf_" << n.getKind() << "_" << n.getId();
      Node op = NodeManager::currentNM()->mkSkolem( ss.str(), typ, "was created by the quantifiers rewriter" );
      std::vector< Node > predArgs;
      predArgs.push_back( op );
      predArgs.insert( predArgs.end(), activeArgs.begin(), activeArgs.end() );
      Node pred = NodeManager::currentNM()->mkNode( APPLY_UF, predArgs );
      Trace("quantifiers-rewrite-cnf-debug") << "Made predicate " << pred << " for " << nt << std::endl;
      //create the bound var list
      Node bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, activeArgs );
      //now, look at the structure of nt
      if( nt.getKind()== kind::NOT ){
        //case for NOT
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[0].notNode() : nt[0] );
          tt << ( i==0 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()== kind::OR ){
        //case for OR
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i].notNode() << pred;
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i];
        }
        tt << pred.notNode();
        defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()== kind::AND ){
        //case for AND
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i] << pred.notNode();
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i].notNode();
        }
        tt << pred;
        defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()== kind::IFF ){
        //case for IFF
        for( int i=0; i<4; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( ( i==0 || i==3 ) ? nt[0].notNode() : nt[0] );
          tt << ( ( i==1 || i==3 ) ? nt[1].notNode() : nt[1] );
          tt << ( ( i==0 || i==1 ) ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()== kind::ITE ){
        //case for ITE
        for( int j=1; j<=2; j++ ){
          for( int i=0; i<2; i++ ){
            NodeBuilder<> tt(OR);
            tt << ( ( j==1 ) ? nt[0].notNode() : nt[0] );
            tt << ( ( i==1 ) ? nt[j].notNode() : nt[j] );
            tt << ( ( i==0 ) ? pred.notNode() : pred );
            defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
          }
        }
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[1].notNode() : nt[1] );
          tt << ( i==0 ? nt[2].notNode() : nt[2] );
          tt << ( i==1 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( kind::FORALL, bvl, tt.constructNode() );
        }
      }else{
        Notice() << "Unhandled Quantifiers CNF: " << nt << std::endl;
      }
      return pred;
    }
  }
}
bool QuantifierEliminate::isRewriteRuleQE(Node n)
{
  return !getRewriteRuleQE(n).isNull();
}
Node QuantifierEliminate::getRewriteRuleQE(Node n)
{
  if( n.getKind()==kind::FORALL && n.getNumChildren()==3 && n[2].getNumChildren()>0)
  {
    return n[2];
  }
  else
  {
    return Node::null();
  }
}
bool QuantifierEliminate::doOperationQE(Node f, bool isNested, int cnfOperation)
{
  if(cnfOperation == 1)
  {
    return true;
  }
  else
  {
    return false;
  }
}
Node QuantifierEliminate::computeOperationQE(Node f, bool isNested, int cnfOperation)
{
  if( f.getKind()==kind::FORALL ){
     Debug("expr-qe") << "Compute operation " << cnfOperation << " on " << f << ", nested = " << isNested << "\n";
     std::vector< Node > args;
     for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
       args.push_back( f[0][i] );
     }
     NodeBuilder<> defs(kind::AND);
     Node n = f[1];
     Node ipl;
     if( f.getNumChildren()==3 )
     {
       ipl = f[2];
     }
     n = computeCNFQE( n, args, defs, false );
     ipl = Node::null();
     Debug("expr-qe") << "Compute Operation: return " << n << ", " << args.size() << "\n";
     if( f[1]==n && args.size()==f[0].getNumChildren() )
     {
       return f;
     }
     else
     {
       if( args.empty() ){
         defs << n;
       }
       else
       {
         std::vector< Node > children;
         children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
         children.push_back( n );
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
    return f;
  }
}
void QuantifierEliminate::convertNodeToCNF(Node n)
{
    Debug("expr-qe") << "converting to CNF " << n << "\n";
    Debug("expr-qe") << "Attributes : " << n[0].hasAttribute(QuantAttrib())  << "\n";
   // int rewriteStatus = 0;
    if( !isRewriteRuleQE(n)  ){
    //  RewriteStatus status = REWRITE_DONE;
     // rewriteStatus = 1;
      Node ret = n;
      //get the arguments
      std::vector< Node > args;
      for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
        args.push_back( n[0][i] );
      }
      //get the instantiation pattern list
      Node ipl;
      if( n.getNumChildren()==3 ){
        ipl = n[2];
      }
      //get the body
      if( n.getKind()== kind::EXISTS ){
        std::vector< Node > children;
          children.push_back( n[0] );
          children.push_back( n[1].negate() );
          if( n.getNumChildren()==3 ){
            children.push_back( n[2] );
          }
          ret = NodeManager::currentNM()->mkNode( kind::FORALL, children );
          ret = ret.negate();
       //   rewriteStatus = 0;
        }
      else
      {
         bool isNested = n[0].hasAttribute(QuantAttrib());
         if( doOperationQE( n, isNested, 1 ) )
         {
            ret = computeOperationQE( n, isNested, 1 );
            Debug("expr-qe")<<"After CNF Operation "<<ret<<"\n";
          }
        }
    }

}*/

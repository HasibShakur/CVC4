//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "expr/QuantifierEliminate.h"
#include "expr/attribute.h"
#include "printer/smt2/smt2_printer.h"
#include "util/output.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::printer;

bool QuantifierEliminate::isLiteralQE( Node n ){
  switch( n.getKind() ){
  case NOT:
    return isLiteralQE( n[0] );
    break;
  case OR:
  case AND:
  case IMPLIES:
  case XOR:
  case ITE:
  case IFF:
    return false;
    break;
  case EQUAL:
    return n[0].getType()!= NodeManager::currentNM()->booleanType();
    break;
  default:
    break;
  }
  return true;
}

bool QuantifierEliminate::isCubeQE( Node n ){
  if( isLiteralQE( n ) ){
    return true;
  }else if( n.getKind()==NOT ){
    return isClauseQE( n[0] );
  }else if( n.getKind()==AND ){
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
bool QuantifierEliminate::isClauseQE( Node n ){
  if( isLiteralQE( n ) ){
    return true;
  }else if( n.getKind()==NOT ){
    return isCubeQE( n[0] );
  }else if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isClauseQE( n[i] ) ){
        return false;
      }
    }
    return true;
  }else if( n.getKind()==IMPLIES ){
    return isCubeQE( n[0] ) && isClauseQE( n[1] );
  }else{
    return false;
  }
}

void QuantifierEliminate::addNodeToOrBuilderQE( Node n, NodeBuilder<>& t ){
  if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      t << n[i];
    }
  }else{
    t << n;
  }
}

Node QuantifierEliminate::computeClauseQE( Node n ){
  Assert( isClauseQE( n ) );
  if( isLiteralQE( n ) ){
    return n;
  }else{
    NodeBuilder<> t(OR);
    if( n.getKind()==NOT ){
      if( n[0].getKind()==NOT ){
        return computeClauseQE( n[0][0] );
      }else{
        //De-Morgan's law
        Assert( n[0].getKind()==AND );
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

void QuantifierEliminate::computeArgsQE( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n ){
  if( n.getKind()==BOUND_VARIABLE ){
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
      Node ncnf = computeCNFQE( nc, args, defs, k!=OR );
      if( k==OR ){
        addNodeToOrBuilderQE( ncnf, t );
      }else{
        t << ncnf;
      }
    }
    if( !forcePred && k==OR ){
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
      Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, activeArgs );
      //now, look at the structure of nt
      if( nt.getKind()==NOT ){
        //case for NOT
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[0].notNode() : nt[0] );
          tt << ( i==0 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()==OR ){
        //case for OR
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i].notNode() << pred;
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i];
        }
        tt << pred.notNode();
        defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()==AND ){
        //case for AND
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i] << pred.notNode();
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i].notNode();
        }
        tt << pred;
        defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()==IFF ){
        //case for IFF
        for( int i=0; i<4; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( ( i==0 || i==3 ) ? nt[0].notNode() : nt[0] );
          tt << ( ( i==1 || i==3 ) ? nt[1].notNode() : nt[1] );
          tt << ( ( i==0 || i==1 ) ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()==ITE ){
        //case for ITE
        for( int j=1; j<=2; j++ ){
          for( int i=0; i<2; i++ ){
            NodeBuilder<> tt(OR);
            tt << ( ( j==1 ) ? nt[0].notNode() : nt[0] );
            tt << ( ( i==1 ) ? nt[j].notNode() : nt[j] );
            tt << ( ( i==0 ) ? pred.notNode() : pred );
            defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
          }
        }
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[1].notNode() : nt[1] );
          tt << ( i==0 ? nt[2].notNode() : nt[2] );
          tt << ( i==1 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else{
        Notice() << "Unhandled Quantifiers CNF: " << nt << std::endl;
      }
      return pred;
    }
  }
}

Node QuantifierEliminate::convertToPrenexQE(Node body, std::vector< Node >& args, bool pol)
{
  if( body.getKind()==FORALL ){
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
          Debug("expr-quantifiereliminate") << "newBody is null in convertToPrenex" << "\n" ;
        }
        Debug("expr-quantifiereliminate") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << "\n";
        return newBody;
      }else{
        return body;
      }
    }else if( body.getKind()==ITE || body.getKind()==XOR || body.getKind()==IFF ){
      return body;
    }else{
      Assert( body.getKind()!=EXISTS );
      bool childrenChanged = false;
      std::vector< Node > newChildren;
      for( int i=0; i<(int)body.getNumChildren(); i++ ){
        bool newPol = body.getKind()==NOT  ? !pol : pol;
        Node n = convertToPrenexQE( body[i], args, newPol );
        newChildren.push_back( n );
        if( n!=body[i] ){
          childrenChanged = true;
        }
      }
      if( childrenChanged ){
        if( body.getKind()==NOT && newChildren[0].getKind()==NOT ){
          return newChildren[0][0];
        }else{
          return NodeManager::currentNM()->mkNode( body.getKind(), newChildren );
        }
      }else{
        return body;
      }
    }
}
Node QuantifierEliminate::convertExistentialToForAllQE(Node f)
{
   Node ret =f;
   if( f.getKind()==EXISTS ){
     std::vector< Node > children;
     children.push_back( f[0] );
     children.push_back( f[1].negate() );
     if( f.getNumChildren()==3 ){
       children.push_back( f[2] );
     }
     ret = NodeManager::currentNM()->mkNode( FORALL, children );
     ret = ret.negate();
     if(ret.isNull())
     {
       Debug("expr-quantifiereliminate") << "ret is null after conversion from existential to forall" << "\n";
     }
     return ret;
   }
   else
   {
     return f;
   }
}
Node QuantifierEliminate::getPrenexExpressionQE(Node f)
{
   Node in = convertExistentialToForAllQE(f);
  //Node in = f;

   if( in.getKind()==FORALL ){
    //  Trace("quantifiers-rewrite-debug") << "Compute operation " << computeOption << " on " << f << ", nested = " << isNested << std::endl;
      std::vector< Node > args;
      for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
        args.push_back( in[0][i] );
     }
    NodeBuilder<> defs(kind::AND);
    Node n = in[1];
    if(n.isNull())
    {
      Debug("expr-quantifiereliminate") << "Node n is null in getPrenexExpression after Node n = in[1]" << "\n";
    }
    n = computeCNFQE(n,args,defs,false);
    n = convertToPrenexQE(n,args, true);
    if(n.isNull())
    {
      Debug("expr-quantifiereliminate") << "Node n is null in getPrenexExpression after Node n = n = convertToPrenex(n,args, true)" << "\n";
    }
    return n;
  }
  else
  {
    return in;
  }
}



/*Node QuantifierEliminate::convertToNNF(Node body)
{
  if( body.getKind()== kind::NOT ){
    if( body[0].getKind()== kind::NOT ){
      return convertToNNF( body[0][0] );
    }else if( isLiteral( body[0] ) ){
      return body;
    }else{
      std::vector< CVC4::Node > children;
      Kind k = body[0].getKind();
      if( body[0].getKind()== kind::OR || body[0].getKind()== kind::AND ){
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          children.push_back( convertToNNF( body[0][i].notNode() ) );
        }
        k = body[0].getKind()== kind::AND ? kind::OR : kind::AND;
      }else if( body[0].getKind()== kind::IFF ){
        for( int i=0; i<2; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( convertToNNF( nn ) );
        }
      }else if( body[0].getKind()== kind::ITE ){
        for( int i=0; i<3; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( convertToNNF( nn ) );
        }
      }else{
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return NodeManager::currentNM()->mkNode( k, children );
    }
  }else if( isLiteral( body ) ){
    return body;
  }else{
    std::vector< CVC4::Node > children;
    bool childrenChanged = false;
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      Node nc = convertToNNF( body[i] );
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
/*CVC4::Node QuantifierEliminate::normalizeBody(CVC4::Node body)
{
  bool rewritten = false;
  CVC4::Node normalized;
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


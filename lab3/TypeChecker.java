import CPP.Absyn.*;
import CPP.*;
import java.util.HashMap;
import java.util.LinkedList;
public class TypeChecker {
  public static enum TypeCode {CInt,CDouble,CBool,CVoid}	
  public static class FunType {
         public LinkedList<TypeCode> args ;
         public TypeCode val ;
         public FunType(TypeCode val,LinkedList<TypeCode> args){
         	   
         	   this.args=args;
         	   this.val=val;
         	 
         	}
         public FunType(TypeCode val){
        	 
        	 
        	 this.args=null;
        	 this.val=val;
         }
         }
         
 
  private static class Env { 
  	private LinkedList<HashMap<String,TypeCode>> scopes;
    private HashMap<String,FunType> signature;
	  public Env() {
	    this.scopes = new LinkedList<HashMap<String,TypeCode>>();
	    this.signature=new HashMap<String,FunType>();
	    LinkedList<TypeCode> l=new LinkedList<TypeCode>();
	    l.addLast(TypeCode.CInt);
	   this.addFun("printInt",new FunType(TypeCode.CVoid,l));

	  
	   LinkedList<TypeCode> l1=new LinkedList<TypeCode>();
	    l1.addLast(TypeCode.CDouble);
	    this.addFun("printDouble",new FunType(TypeCode.CVoid,l1));
	    this.addFun("readInt",new FunType(TypeCode.CInt));
	    this.addFun("reandDouble",new FunType(TypeCode.CDouble));
	  }
    
	  public TypeCode lookupVar(String x) {
	    for (HashMap<String,TypeCode> scope : scopes) {
		       TypeCode t = scope.get(x);
		    if (t != null)
		      return t;
	      }
	     throw new TypeException("Unknown variable " + x + ".");
      }
    public FunType lookupFun(String fun){
    	   FunType ft=signature.get(fun);
    	   if(ft!=null)
    	     return ft;
    	   else
    	     throw new TypeException("Unknown function  "+fun);
    	 } 

	  public void addVar(String x, TypeCode t) {
	    if (scopes.getFirst().containsKey(x))
		      throw new TypeException("Variable " + x 
					+ " is already declared in this scope.");
	    else
	       scopes.getFirst().put(x,t);
	  }
	  public void addFun(String x,FunType ft){
	  	
	  	if(signature.get(x)!=null)
	  	  throw new TypeException("function "+x+ " already exists ");
	  	else
	  	  signature.put(x,ft);  
	  	
	  	}

	   public void enterScope() {
	     scopes.addFirst(new HashMap<String,TypeCode>());
    	 }

	    public void leaveScope() {
	    scopes.removeFirst();
	  }
    }
  public static class AnnoExp {
      public final TypeCode typecode_ ;
      public final Exp exp_ ;

   public AnnoExp(TypeCode t, Exp e){
   	          typecode_ = t ; 
   	          exp_ = e ;
   	 } 
}
  
	public void typecheck(Program p) {
		  PDefs program=(PDefs)p;
		  Env   environment=new Env();
		  
		  for(Def d: program.listdef_){
		  	    LinkedList<TypeCode> argType_List=new LinkedList<TypeCode>();
		  	    DFun df=(DFun)d;
		  	    for(Arg g:df.listarg_){
		  	    	  ADecl ad=(ADecl)g;
		  	    	  argType_List.addLast(type2TypeCode(ad.type_)); 
		  	    	}
		  	     FunType ft=new FunType(type2TypeCode(df.type_),argType_List);
		  	     environment.addFun(df.id_,ft);   
		  	}
		  for(Def d: program.listdef_){
		  	     checkDef(d,environment);
		  	}
		}
	private void checkDef(Def d,Env environment){
		   environment.enterScope();
		   d.accept(new DefChecker(),environment);
		   
    }
   private class DefChecker implements Def.Visitor<Def,Env>{
   	public Def visit(CPP.Absyn.DFun d, Env environment)
    {
      environment.addVar("ThisFunction",type2TypeCode(d.type_));
      for (Arg x : d.listarg_) {
      	   checkArg(x,environment);
      }
     

      for (int i=0;i<d.liststm_.size();i++) {
      	   
          d.liststm_.set(i,checkStm(d.liststm_.get(i),environment)); 
         
      }
          
      return null;
    }
   	}
    private void checkArg(Arg g,Env environment){
    	
    	        g.accept(new argChecker(),environment);
    	}   	
 
   private class argChecker implements Arg.Visitor<Arg,Env>
  {
    public Arg visit(CPP.Absyn.ADecl p, Env environment)
    {
      environment.addVar(p.id_,type2TypeCode(p.type_));
      return null;
    }
  
		
		}
		public Stm checkStm(Stm s,Env environment){
			     return s.accept(new stmChecker(),environment);
			}
			
	 private class  stmChecker implements Stm.Visitor<Stm,Env>{
	 	public Stm visit(CPP.Absyn.SExp p, Env environment)
    {
	 		AnnoExp ae=inferExp(p.exp_,environment);
           
           return new SExp(ae.exp_);
    }
    public Stm visit(CPP.Absyn.SDecls p, Env environment)
    {
        for (String x : p.listid_) {
         environment.addVar(x,type2TypeCode(p.type_));
      }
        
      return p;
    }
    public Stm visit(CPP.Absyn.SInit p, Env environment)
    {  
    	     AnnoExp ae= checkExp(p.exp_,type2TypeCode(p.type_),environment);
             environment.addVar(p.id_, ae.typecode_);
             
            return new SInit(p.type_,p.id_,ae.exp_);
    }
    public Stm visit(CPP.Absyn.SReturn p, Env environment)
    {
           TypeCode t=environment.lookupVar("ThisFunction");            
           AnnoExp ae=checkExp(p.exp_,t,environment);
             
           return new SReturn(ae.exp_);
    }
    public Stm visit(CPP.Absyn.SWhile p,Env environment)
    {
         	AnnoExp ae=checkExp(p.exp_,TypeCode.CBool,environment);
            Stm s=checkStm(p.stm_,environment);

           return new SWhile(ae.exp_,s);
    }
    public Stm visit(CPP.Absyn.SBlock p, Env environment)
    {
         environment.enterScope();
        for (int i=0;i<p.liststm_.size();i++) {
        	 p.liststm_.set(i,checkStm(p.liststm_.get(i),environment));
        }
        environment.leaveScope();
        return p;
    }
    public Stm visit(CPP.Absyn.SIfElse p, Env environment)
    {
    	AnnoExp ae=checkExp(p.exp_,TypeCode.CBool,environment);
        Stm s1=checkStm(p.stm_1,environment);
        Stm s2=checkStm(p.stm_2,environment); 
       
      return new SIfElse(ae.exp_,s1,s2);
    }

	 	
	 	}
	 private AnnoExp   checkExp(Exp e,TypeCode t,Env environment){
		      AnnoExp tf=inferExp(e,environment);
	 	         if (tf.typecode_ != t) {
	                throw new TypeException(PrettyPrinter.print(e) 
				                    + " has type " + tf 
				                    + " expected " + t);
	                        }
	 	     return tf;
	 	}
	 private AnnoExp inferExp(Exp e,Env environment){
	 	
	 	      return e.accept(new expInferer(),environment);
	 	
	 	}
	 private class expInferer implements Exp.Visitor<AnnoExp,Env>{
	 	   public AnnoExp visit(CPP.Absyn.ETrue p, Env environment)
    {
           return  new AnnoExp(TypeCode.CBool,new AnnoType(typeCode2Type(TypeCode.CBool),p));
    }
    public AnnoExp visit(CPP.Absyn.EFalse p,Env environment)
    {
    	  return new AnnoExp(TypeCode.CBool,new AnnoType(typeCode2Type(TypeCode.CBool),p));
    }
    public AnnoExp visit(CPP.Absyn.EInt p,Env environment)
    {
           return new AnnoExp(TypeCode.CInt,new AnnoType(typeCode2Type(TypeCode.CInt),p));
    }
    public AnnoExp visit(CPP.Absyn.EDouble p,Env environment)
    { 
    	    return new AnnoExp(TypeCode.CDouble,new AnnoType(typeCode2Type(TypeCode.CDouble),p));
    }
    public AnnoExp visit(CPP.Absyn.EId p,Env environment)
    {
         TypeCode t=environment.lookupVar(p.id_);
        return new AnnoExp(t,new AnnoType(typeCode2Type(t),p));
    }
    public AnnoExp visit(CPP.Absyn.EApp p, Env environment)
    {
           FunType ft=environment.lookupFun(p.id_);
        LinkedList<TypeCode> ft_list=ft.args;
       int len;
       if(ft_list==null)
         len=0;
       else
         len=ft_list.size();
       
       TypeCode type1=null;
       TypeCode type2=null;
     
       if(len==p.listexp_.size()){
      	 
        for (int i=0;i<len;i++) {
           type1=inferExp(p.listexp_.get(i),environment).typecode_;
           AnnoExp e=inferExp(p.listexp_.get(i),environment);
           p.listexp_.set(i, new AnnoType(typeCode2Type(type1),e.exp_));
            
           type2=ft_list.get(i);
           if(type1!=type2){
           	 throw new TypeException("u have given the wrong type of arguments of function "+p.id_);
           	}
        }
     }
      else 
         throw new TypeException("the function "+p.id_+" is not given right number of arguments");
      
      
      return new AnnoExp(ft.val,new AnnoType(typeCode2Type(ft.val),p));
    }
    public AnnoExp visit(CPP.Absyn.EPIncr p,Env environment)
    {      
    	     if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EPIncr must be a variable");
    	     	} 
           TypeCode type=environment.lookupVar(((EId)p.exp_).id_);

           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return new AnnoExp(type,new AnnoType(typeCode2Type(type),p));
    }
    public AnnoExp visit(CPP.Absyn.EPDecr p, Env environment)
    {
    	     
    	     if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EPDecr must be a variable");
    	     	} 
    	     	
           TypeCode type=environment.lookupVar(((EId)p.exp_).id_);
           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return    new AnnoExp(type,new AnnoType(typeCode2Type(type),p));
    }
    public AnnoExp visit(CPP.Absyn.EIncr p, Env environment)
    {      if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EIncr must be a variable");
    	     	} 
    	     TypeCode type=environment.lookupVar(((EId)p.exp_).id_);
           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return new AnnoExp(type,new AnnoType(typeCode2Type(type),p));
    }
    public AnnoExp visit(CPP.Absyn.EDecr p, Env environment)
    {      if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EDecr must be a variable");
    	     	} 
    	     TypeCode type=environment.lookupVar(((EId)p.exp_).id_);
           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return new AnnoExp(type,new AnnoType(typeCode2Type(type),p));
    }
    public AnnoExp visit(CPP.Absyn.ETimes p, Env environment)
    {
           AnnoExp type1=inferExp(p.exp_1,environment);
           AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
           	 return new AnnoExp(TypeCode.CInt,new AnnoType(typeCode2Type(TypeCode.CInt),new ETimes(type1.exp_,type2.exp_)));
           	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
           	
           	 return new AnnoExp(TypeCode.CDouble, new AnnoType(typeCode2Type(TypeCode.CDouble),new ETimes(type1.exp_,type2.exp_)));
           	}
            else throw new TypeException("the operant must be both int or double");

    }
    public AnnoExp visit(CPP.Absyn.EDiv p,Env environment)
    {
    	     
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
           	 return new AnnoExp(TypeCode.CInt,new AnnoType(typeCode2Type(TypeCode.CInt),new EDiv(type1.exp_,type2.exp_)));
                   	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
            	 return new AnnoExp(TypeCode.CDouble, new AnnoType(typeCode2Type(TypeCode.CDouble),new EDiv(type1.exp_,type2.exp_)));
            	            	}
           else throw new TypeException("the operant must be both int or double");
    }
    public AnnoExp visit(CPP.Absyn.EPlus p,Env environment)
    {   
    	    
    	AnnoExp  type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
             	 return new AnnoExp(TypeCode.CInt,new AnnoType(typeCode2Type(TypeCode.CInt),new EPlus(type1.exp_,type2.exp_)));
      	  }
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
           	
           	 return new AnnoExp(TypeCode.CDouble, new AnnoType(typeCode2Type(TypeCode.CDouble),new EPlus(type1.exp_,type2.exp_)));
                    	}
           else throw new TypeException("the operant must be both int or double");
    }
    public AnnoExp visit(CPP.Absyn.EMinus p,Env environment)
    {
    	
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
             	 return new AnnoExp(TypeCode.CInt,new AnnoType(typeCode2Type(TypeCode.CInt),new EMinus(type1.exp_,type2.exp_)));
             	      	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
           	
            	 return new AnnoExp(TypeCode.CDouble, new AnnoType(typeCode2Type(TypeCode.CDouble),new EMinus(type1.exp_,type2.exp_)));
            	       	}
           else throw new TypeException("the operant must be both int or double");
    }
    public AnnoExp visit(CPP.Absyn.ELt p,Env environment)
    {
    	    
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
            	 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new ELt(type1.exp_,type2.exp_)));
            	         	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
            	 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new ELt(type1.exp_,type2.exp_)));
            	         	}
           else throw new TypeException("the operant must be both int or double");
    }
    public AnnoExp visit(CPP.Absyn.EGt p, Env environment)
    {
    	    
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
           	 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new EGt(type1.exp_,type2.exp_)));
                   	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
           	 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new EGt(type1.exp_,type2.exp_)));
             
           }
           else throw new TypeException("the operant must be both int or double");
    	
    }
    public AnnoExp visit(CPP.Absyn.ELtEq p, Env environment)
    {
    	     
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
          	 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new ELtEq(type1.exp_,type2.exp_)));
                   	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
          	 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new ELtEq(type1.exp_,type2.exp_)));
                  	}
           	
           else throw new TypeException("the operant must be both int or double");
    }
    public AnnoExp visit(CPP.Absyn.EGtWq p, Env environment)
    {
    	 
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
        		 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new EGtWq(type1.exp_,type2.exp_)));
                      	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
        		 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new EGtWq(type1.exp_,type2.exp_)));
                      	}
           else throw new TypeException("the operant must be both int or double ");
    }
    public AnnoExp visit(CPP.Absyn.EEq p, Env environment)
    {
        
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
      		 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new EEq(type1.exp_,type2.exp_)));
      	       	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
      		 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new EEq(type1.exp_,type2.exp_)));
      	       	}
           else throw new TypeException("the operant must be both int or double ");
    }
    public AnnoExp visit(CPP.Absyn.ENEq p,Env environment)
    {
      
    	AnnoExp type1=inferExp(p.exp_1,environment);
    	AnnoExp  type2=inferExp(p.exp_2,environment);
           if(type1.typecode_==TypeCode.CInt&&type2.typecode_==TypeCode.CInt){
        		 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new ENEq(type1.exp_,type2.exp_)));
        		             	}
           else if(type1.typecode_==TypeCode.CDouble&&type2.typecode_==TypeCode.CDouble){
        		 return new AnnoExp(TypeCode.CBool, new AnnoType(typeCode2Type(TypeCode.CBool),new ENEq(type1.exp_,type2.exp_)));
        		            	}
           else throw new TypeException("the operant must be both int or double ");
    }
    public AnnoExp visit(CPP.Absyn.EAnd p, Env environment)
    {
        
    	AnnoExp ae1=checkExp(p.exp_1,TypeCode.CBool,environment);
    	AnnoExp ae2=checkExp(p.exp_2,TypeCode.CBool,environment);
                 
             return new AnnoExp(TypeCode.CBool,new AnnoType(typeCode2Type(TypeCode.CBool),new EAnd(ae1.exp_,ae2.exp_)));
 
    }
    public AnnoExp visit(CPP.Absyn.EOr p,Env environment)
    {
    	AnnoExp ae1=checkExp(p.exp_1,TypeCode.CBool,environment);
    	AnnoExp ae2=checkExp(p.exp_2,TypeCode.CBool,environment);
             
        return new AnnoExp(TypeCode.CBool,new AnnoType(typeCode2Type(TypeCode.CBool),new EOr(ae1.exp_,ae2.exp_)));
      
    }
    public AnnoExp visit(CPP.Absyn.EAss p, Env environment)
    {
            if(!(p.exp_1 instanceof EId)){
    	     	 throw new TypeException("left operant of assertion must be a variable");
    	     	}    
            AnnoExp type=inferExp(p.exp_2,environment);
            AnnoExp  ae=checkExp(p.exp_1,type.typecode_,environment);
          
            return new AnnoExp(type.typecode_,new AnnoType(typeCode2Type(type.typecode_),new EAss(ae.exp_,type.exp_)));
    }
	@Override
	public AnnoExp visit(AnnoType p, Env arg) {
		// TODO Auto-generated method stub
		return new AnnoExp(type2TypeCode(p.type_),p);
	}
	 	
	 	}	
	  	
		
		
	private   Type     typeCode2Type(TypeCode tc){
		    if(tc.equals(TypeCode.CBool)){
		    	
		    	return new Type_bool();
		    }
		    else if(tc.equals(TypeCode.CDouble)){
		    	return new Type_double();
		    }
		    else if(tc.equals(TypeCode.CInt)){
		       return new Type_int();
		    }
		    else 
		      return new Type_void();
		
	}	
	private TypeCode  type2TypeCode(Type t){
		   
		       return t.accept(new TypeTransfer(),null);
		
		}
	
	
  private class TypeTransfer implements Type.Visitor<TypeCode,Env>
  {
    public TypeCode visit(CPP.Absyn.Type_bool p, Env arg)
    {
             return TypeCode.CBool;

    }
    public TypeCode visit(CPP.Absyn.Type_int p, Env arg)
    {      
    	      return TypeCode.CInt;
    }
    public TypeCode visit(CPP.Absyn.Type_double p, Env arg)
    {
            return TypeCode.CDouble;
    }
    public TypeCode visit(CPP.Absyn.Type_void p, Env arg)
    {
           return TypeCode.CVoid;
    }
	
		
}
}
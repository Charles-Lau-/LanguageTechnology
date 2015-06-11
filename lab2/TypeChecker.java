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
     

      for (Stm x : d.liststm_) {
      	   
          checkStm(x,environment); 
         
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
		public void checkStm(Stm s,Env environment){
			     s.accept(new stmChecker(),environment);
			}
			
	 private class  stmChecker implements Stm.Visitor<Stm,Env>{
	 	public Stm visit(CPP.Absyn.SExp p, Env environment)
    {
         inferExp(p.exp_,environment);
         return null;
    }
    public Stm visit(CPP.Absyn.SDecls p, Env environment)
    {
        for (String x : p.listid_) {
         environment.addVar(x,type2TypeCode(p.type_));
      }

      return null;
    }
    public Stm visit(CPP.Absyn.SInit p, Env environment)
    {  
    	       checkExp(p.exp_,type2TypeCode(p.type_),environment);
             environment.addVar(p.id_,type2TypeCode(p.type_));  
             return null;
    }
    public Stm visit(CPP.Absyn.SReturn p, Env environment)
    {
           TypeCode t=environment.lookupVar("ThisFunction");            
           checkExp(p.exp_,t,environment);
             
           return null;
    }
    public Stm visit(CPP.Absyn.SWhile p,Env environment)
    {
           checkExp(p.exp_,TypeCode.CBool,environment);
           checkStm(p.stm_,environment);

          return null;
    }
    public Stm visit(CPP.Absyn.SBlock p, Env environment)
    {
         environment.enterScope();
        for (Stm x : p.liststm_) {
        	 checkStm(x,environment);
        }
        environment.leaveScope();
        return null;
    }
    public Stm visit(CPP.Absyn.SIfElse p, Env environment)
    {
        checkExp(p.exp_,TypeCode.CBool,environment);
        checkStm(p.stm_1,environment);
        checkStm(p.stm_2,environment); 
       
      return null;
    }

	 	
	 	}
	 private void   checkExp(Exp e,TypeCode t,Env environment){
	 	         TypeCode tf=inferExp(e,environment);
	 	         if (tf != t) {
	                throw new TypeException(PrettyPrinter.print(e) 
				                    + " has type " + tf 
				                    + " expected " + t);
	                        }
	 	}
	 private TypeCode inferExp(Exp e,Env environment){
	 	
	 	      return e.accept(new expInferer(),environment);
	 	
	 	}
	 private class expInferer implements Exp.Visitor<TypeCode,Env>{
	 	   public TypeCode visit(CPP.Absyn.ETrue p, Env environment)
    {
       return  TypeCode.CBool;
    }
    public TypeCode visit(CPP.Absyn.EFalse p,Env environment)
    {
    	 return TypeCode.CBool;
    }
    public TypeCode visit(CPP.Absyn.EInt p,Env environment)
    {
       return TypeCode.CInt;
    }
    public TypeCode visit(CPP.Absyn.EDouble p,Env environment)
    { 
    	  return TypeCode.CDouble;
    }
    public TypeCode visit(CPP.Absyn.EId p,Env environment)
    {
       
      return environment.lookupVar(p.id_);
    }
    public TypeCode visit(CPP.Absyn.EApp p, Env environment)
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
           type1=inferExp(p.listexp_.get(i),environment);
           type2=ft_list.get(i);
           if(type1!=type2){
           	 throw new TypeException("u have given the wrong type of arguments of function "+p.id_);
           	}
        }
     }
      else 
         throw new TypeException("the function "+p.id_+" is not given right number of arguments");

      return ft.val;
    }
    public TypeCode visit(CPP.Absyn.EPIncr p,Env environment)
    {      
    	     if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EPIncr must be a variable");
    	     	} 
           TypeCode type=environment.lookupVar(((EId)p.exp_).id_);

           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return type;
    }
    public TypeCode visit(CPP.Absyn.EPDecr p, Env environment)
    {
    	     if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EPDecr must be a variable");
    	     	} 
    	     	
           TypeCode type=environment.lookupVar(((EId)p.exp_).id_);
           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return type;
    }
    public TypeCode visit(CPP.Absyn.EIncr p, Env environment)
    {      if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EIncr must be a variable");
    	     	} 
    	     TypeCode type=environment.lookupVar(((EId)p.exp_).id_);
           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return type;
    }
    public TypeCode visit(CPP.Absyn.EDecr p, Env environment)
    {      if(!(p.exp_ instanceof EId)){
    	     	 throw new TypeException("operant of EDecr must be a variable");
    	     	} 
    	     TypeCode type=environment.lookupVar(((EId)p.exp_).id_);
           if(type!=TypeCode.CDouble&&type!=TypeCode.CInt){
           	 throw new TypeException("the operant must be numeric");
           	}
           return type;
    }
    public TypeCode visit(CPP.Absyn.ETimes p, Env environment)
    {
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CInt;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
           	
           	 return  TypeCode.CDouble;
           	}
           else throw new TypeException("the operant must be both int or double");

    }
    public TypeCode visit(CPP.Absyn.EDiv p,Env environment)
    {
    	     
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CInt;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
           	
           	 return  TypeCode.CDouble;
           	}
           else throw new TypeException("the operant must be both int or double");
    }
    public TypeCode visit(CPP.Absyn.EPlus p,Env environment)
    {   
    	    
           TypeCode  type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CInt;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
           	
           	 return  TypeCode.CDouble;
           	}
           else throw new TypeException("the operant must be both int or double");
    }
    public TypeCode visit(CPP.Absyn.EMinus p,Env environment)
    {
    	
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CInt;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
           	
           	 return  TypeCode.CDouble;
           	}
           else throw new TypeException("the operant must be both int or double");
    }
    public TypeCode visit(CPP.Absyn.ELt p,Env environment)
    {
    	    
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CBool;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
             return  TypeCode.CBool;
           	}
           else throw new TypeException("the operant must be both int or double");
    }
    public TypeCode visit(CPP.Absyn.EGt p, Env environment)
    {
    	    
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CBool;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
             return  TypeCode.CBool;
           	}
           else throw new TypeException("the operant must be both int or double");
    	
    }
    public TypeCode visit(CPP.Absyn.ELtEq p, Env environment)
    {
    	     
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CBool;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
             return  TypeCode.CBool;
           	}
           	
           else throw new TypeException("the operant must be both int or double");
    }
    public TypeCode visit(CPP.Absyn.EGtWq p, Env environment)
    {
    	 
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CBool;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
             return  TypeCode.CBool;
           	}
           else throw new TypeException("the operant must be both int or double ");
    }
    public TypeCode visit(CPP.Absyn.EEq p, Env environment)
    {
        
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CBool;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
             return  TypeCode.CBool;
           	}
           else throw new TypeException("the operant must be both int or double ");
    }
    public TypeCode visit(CPP.Absyn.ENEq p,Env environment)
    {
      
           TypeCode type1=inferExp(p.exp_1,environment);
           TypeCode  type2=inferExp(p.exp_2,environment);
           if(type1==TypeCode.CInt&&type2==TypeCode.CInt){
           	 return TypeCode.CBool;
           	}
           else if(type1==TypeCode.CDouble&&type2==TypeCode.CDouble){
             return  TypeCode.CBool;
           	}
           else throw new TypeException("the operant must be both int or double ");
    }
    public TypeCode visit(CPP.Absyn.EAnd p, Env environment)
    {
        
             checkExp(p.exp_1,TypeCode.CBool,environment);
             checkExp(p.exp_2,TypeCode.CBool,environment);
                 
             return TypeCode.CBool;
 
    }
    public TypeCode visit(CPP.Absyn.EOr p,Env environment)
    {
    	       checkExp(p.exp_1,TypeCode.CBool,environment);
               checkExp(p.exp_2,TypeCode.CBool,environment);
             
              return TypeCode.CBool;
    }
    public TypeCode visit(CPP.Absyn.EAss p, Env environment)
    {
            if(!(p.exp_1 instanceof EId)){
    	     	 throw new TypeException("left operant of assertion must be a variable");
    	     	}    
            TypeCode type=inferExp(p.exp_2,environment);
            checkExp(p.exp_1,type,environment);
          
            return type;
    }
	 	
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

import java.util.HashMap;
import java.util.LinkedList;

 
import CPP.Absyn.*;
 

public class Interpreter {
	 public static String flag="";
	 public static abstract class Value{
		  
		  public String myType(){return "";}
	  	  public Integer getInt(){throw new RuntimeException(this+" is not a integer");}
	  	  public Boolean getBool(){throw new RuntimeException(this +" is not a bool");}
	      public Closure getClosure(){throw new RuntimeException(this + "is not a closure");}
		  public Exp     getExp(){throw new RuntimeException(this +"is not a expression");}
	      public static class intValue extends Value{
			   private Integer i;
			   public intValue(Integer i){this.i= i;}
			   public String myType(){return "integer";}
               public Integer getInt(){return this.i;}			    
		  }
	      public static class expValue extends Value{
	    	  private Exp e;
	    	  public expValue(Exp e){this.e=e;}
	    	  public String myType(){return "expression";}
	    	  public Exp    getExp(){return this.e;}
	      }
		  public static class boolValue extends Value{
			  private Boolean b;
			  public boolValue(Boolean b){this.b=b;}
			  public String myType(){return "bool";}
			  public Boolean getBool(){return this.b;}
		  }
		  public static class closureValue extends Value{
			    private Closure c;
			    public closureValue(Closure c){this.c=c;}
			    public String myType(){return "closure";}
			    public Closure getClosure(){return this.c;}
		  }
	 } 
 	 private static class Closure{
 		   private EAbs abstraction;
 		   private HashMap<String,Value> hm;
 		   public Closure(EAbs a,HashMap<String,Value> h){this.abstraction=a;this.hm=h;}
 		   public EAbs getAbstraction(){return this.abstraction;}
 		   public HashMap<String,Value> getHashMap(){return this.hm;}
 	 }
	 private static class Env{
      public LinkedList<HashMap<String,Value>> scopes;
	  public HashMap<String,Def> signature;
	  public Env() {
		    this.scopes = new LinkedList<HashMap<String,Value>>();
		    this.signature=new HashMap<String,Def>();	 
		     }
	    
		public Value lookupVar(String var){
			 for (HashMap<String,Value> scope : scopes) {
			        Value v = scope.get(var);
			       if (v != null)
			        return v;
 	           }
			 throw new RuntimeException("unkonwn variable "+ var);  
			
		}
        
	    public Def lookupFun(String fun){
	    	   Def d=signature.get(fun);
	    	   if(d!=null)
	    	     return d;
	    	   else
	    	     throw new RuntimeException("Unknown function  "+fun);
	    	 }
	    public Object lookup(String var){
	    	 for (HashMap<String,Value> scope : scopes) {
				        Value v = scope.get(var);
				       if (v != null)
				        return v;
	    	   }
	    	   Def d=signature.get(var);
	       	   if(d!=null)
	    	      return d;
	    	    else
	    	      throw new RuntimeException("can't find function  "+var);
	    	  }
	 
	  public void addVar(String x,Value v) {

	       scopes.getFirst().put(x,v);
	  }
	  public void addFun(String x,Def d){
	  	if(signature.get(x)!=null)
	  	  throw new RuntimeException("function "+x+ " already exists ");
	  	else
	  	  signature.put(x,d);  
	  	
	  	}

	   public void enterScope() {
	     scopes.addLast(new HashMap<String,Value>());
   	  }

	    public void leaveScope() {
	    scopes.removeLast();
	  }

	 }
	  public void interpret(Program p,String flag){
		    this.flag=flag;
		    Env environment=new Env();
		    Prog pro=(Prog)p;
		    for(Def d:pro.listdef_){
			     DDef dd=(DDef)d;
			     environment.addFun(dd.ident_, d);
		    }
		   DDef main=(DDef)environment.lookupFun("main"); 
		   environment.enterScope();
		  Value v=evalExp(main.exp_,environment);
		  
		   environment.leaveScope();
	 		
	   if(flag.equals("-v")){	
		 	
		   if(v instanceof Value.intValue)
			  System.out.println(((Value.intValue)v).getInt());
		  else
		     throw new RuntimeException("the return type of main should be integer");
	   }
	   else{
		  if(v instanceof Value.intValue){
			  System.out.println(((Value.intValue)v).getInt());
		  }
		   else if(v instanceof Value.expValue){
				   Value.expValue ve=(Value.expValue)v;  
			    
			    if(ve.getExp() instanceof EInt){
			    	  System.out.println(((EInt)ve.getExp()).integer_);
			 		  
			      }  
			      else
			    	  throw new RuntimeException("the return type of main should be integer");
			  	  
		   }
		   else
			   throw new RuntimeException("the return type of main should be integer");
			
		   
	   }
	   }
	 
	public Value evalExp(Exp e,Env environment){
		  
		return e.accept(new expEvaluator(),environment);
	} 
 
	  public class expEvaluator implements Exp.Visitor<Value,Env>
	  {
	    public Value visit(CPP.Absyn.EVar p,Env environment)
	    {    
	    	   Object obj=environment.lookup(p.ident_);
	    	    
	    	   if(obj instanceof Value){
	    		  		
	   	    	 if(flag.equals("-v"))
	    		    return (Value)obj;
	   	    	 else
	   	    		 return ((Value.expValue)obj).getExp().accept(new expEvaluator(), environment);
	    	   }
	    	   else{
	    		   DDef dd=(DDef)obj;
	    		if(dd.listident_.size()!=0){	
	   	    	   
	    		   EAbs ea= new EAbs(dd.listident_.getLast(),dd.exp_);
	    		    
	    		   for(int i=dd.listident_.size()-2;i>=0;i--){
     	    	       
	    			    ea=new EAbs(dd.listident_.get(i),ea);
     	    	      
	    		      } 
	    		   
	    		    
	   	    	
	               return  new Value.closureValue(new Closure(ea,new HashMap<String,Value>()));
	    	   }
	    	   
	    	   else
	    		    return dd.exp_.accept(new expEvaluator(),environment);
	    	   }
	    	   }
	    	    
	    	   
	     
	    public Value visit(CPP.Absyn.EInt p, Env environment)
	    {
   

	       return new Value.intValue(p.integer_);
	    }
	    public Value visit(CPP.Absyn.EApp p, Env environment)
	    {  
            
              if(Interpreter.flag.equals("-v")){
	    	 
 	    		   Value.closureValue v1=(Value.closureValue) p.exp_1.accept(new expEvaluator(), environment);
	    		   Closure c=v1.getClosure();
	    		   c.getHashMap().put(c.getAbstraction().ident_,p.exp_2.accept(new expEvaluator(),environment));
	    		   
	    		   for(String key:c.getHashMap().keySet()){
	    			   environment.addVar(key, c.getHashMap().get(key));
	    		   }
	    		   
	    		   Value v2=c.getAbstraction().exp_.accept(new expEvaluator(), environment);   
	             
	    		   if(v2 instanceof Value.closureValue)
	    		   {
	    			   for(String key:c.getHashMap().keySet()){
		    			   v2.getClosure().getHashMap().put(key, c.getHashMap().get(key));
		    		   }   
	    			   
	    		   } 
	              return v2; 
              }
              else{

            	  Value.closureValue v1=(Value.closureValue) p.exp_1.accept(new expEvaluator(), environment);
	    		  Closure c=v1.getClosure();
	    	      c.getHashMap().put(c.getAbstraction().ident_, new Value.expValue(p.exp_2));
	    	     
	    	       for(String key:c.getHashMap().keySet()){
	    			   environment.addVar(key, c.getHashMap().get(key));
	    		   }
	    		   
	    	      Value v2=c.getAbstraction().exp_.accept(new expEvaluator(), environment);
                  
	    	      if(v2 instanceof Value.closureValue)
	    		   {
	    			   for(String key:c.getHashMap().keySet()){
		    			   v2.getClosure().getHashMap().put(key, c.getHashMap().get(key));
		    		   }   
	    			   
	    		   }
	    	      return v2;
              }
              }
 
     public Value visit(CPP.Absyn.EAdd p,Env environment)
	    {

            Value v1=p.exp_1.accept(new expEvaluator(),environment);
            Value v2=p.exp_2.accept(new expEvaluator(),environment);
	       
          if(v1 instanceof Value.intValue&&v2 instanceof Value.intValue)
            return new Value.intValue(((Value.intValue)v1).getInt()+((Value.intValue)v2).getInt());
	     else
	    	throw new RuntimeException("the type should be integer");
		
	    }
	    public Value visit(CPP.Absyn.ESub p,Env environment)
	    {
                Value v1=p.exp_1.accept(new expEvaluator(),environment);
	            Value v2=p.exp_2.accept(new expEvaluator(),environment);
		       
	          if(v1 instanceof Value.intValue&&v2 instanceof Value.intValue)
	            return new Value.intValue(((Value.intValue)v1).getInt()-((Value.intValue)v2).getInt());
		     else
		    	throw new RuntimeException("the type should be integer");
		  }
	    public Value visit(CPP.Absyn.ELt p,Env environment)
	    {
        
	          Value.intValue int1=(Value.intValue) p.exp_1.accept(new expEvaluator(),environment);
	          Value.intValue int2=(Value.intValue) p.exp_2.accept(new expEvaluator(),environment);
	 
	           if(int1.myType().equals("integer")&&int2.myType().equals("integer"))
	         	          return new Value.boolValue(int1.getInt()<int2.getInt());
		      else
		    	  throw new RuntimeException("the type should be integer");
	    }
	    public Value visit(CPP.Absyn.EIf p,Env environment)
	    {
	    	Value condition=p.exp_1.accept(new expEvaluator(), environment);
	        Value return_v=null;
	    	if(condition.myType().equals("bool")){
	                Value.boolValue bv=(Value.boolValue)condition;
	                if(bv.getBool()){
	                     return_v=p.exp_2.accept(new expEvaluator(),environment);
	                }
	                else
	                	return_v=p.exp_3.accept(new expEvaluator(), environment);
	             return return_v;     
	      }
	      else
	    	  throw new RuntimeException("the condition should be boolean");
	     }
	    public Value visit(CPP.Absyn.EAbs p,Env environment)
	    {
	    	HashMap<String,Value> hm=new HashMap<String,Value>();
	    	
	    try{
	    	
	    	hm.put(p.ident_, environment.lookupVar(p.ident_));
	    }
	    catch(Exception e){}
	    	
	    	return new Value.closureValue(new Closure(p,hm));
	    }

	  }
	  }     


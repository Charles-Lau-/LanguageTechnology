import CPP.Absyn.*;
import java.util.*;
public class Interpreter {
  static  Scanner scan = new Scanner(System.in);
   
  private  static abstract  class Value{
  	  
  	  public String myType(){return "";}
  	  public void  increase(){new RuntimeException(this +" is not numeric");}
  	  public void decrease(){new RuntimeException(this+" is not numeric");}
  	  public Integer getInt(){throw new RuntimeException(this+" is not a integer");}
  	  public Double  getDouble(){throw new RuntimeException(this+" is not a double");}
  	  public Boolean    getBool(){throw new RuntimeException(this +" is not a bool");}
         
  	  public static class Undefined extends Value{
  	  	  public Undefined(){}
  	  	  public String myType(){return "undefined";} 
  	  	}
  	  public static class IntValue extends Value{
  	  	 private Integer i;
  	  	 public IntValue(Integer i){this.i=i;}
  	  	 public Integer getInt() {return this.i;} 
  	  	 public String myType() {return "integer";}
  	  	 public void increase() {this.i=this.i+1;}
  	  	 public void decrease(){this.i=this.i+1;}
  	  	}
  	  public static class DoubleValue extends Value{
  	  	private Double d;
  	  	public DoubleValue(Double d){this.d=d;}
  	  	public Double getDouble() {return this.d;}
  	  	public String myType() {return "double";}
  	  	public void increase(){this.d=this.d+1.0;}
  	  	public void decrease(){this.d=this.d-1.0;}
  	  	}
  	  public static class BoolValue extends Value{
        private Boolean b;
        public BoolValue(Boolean b){this.b=b;}
        public Boolean getBool(){return this.b;}
        public String myType(){return "bool";}
        	}
     	 }
   
   
   private static class Env { 
  	public LinkedList<HashMap<String,Value>> scopes;
        public HashMap<String,Def> signature;
	  public Env() {
	    this.scopes = new LinkedList<HashMap<String,Value>>();
	    this.signature=new HashMap<String,Def>();	 
	     }
    
	public Value lookupVar(String x) {
	    for (HashMap<String,Value> scope : scopes) {
		        Value v = scope.get(x);
		       if (v != null)
		    return v;
	    }
	    throw new RuntimeException("Unknown variable " + x + " in " + scopes);
	}

    public Def lookupFun(String fun){
    	   Def d=signature.get(fun);
    	   if(d!=null)
    	     return d;
    	   else
    	     throw new RuntimeException("Unknown function  "+fun);
    	 } 
  public void setVar(String x, Value v) {
	    for (HashMap<String,Value> scope : scopes) {
		
   if (scope.containsKey(x)) {
		    scope.put(x,v);
		    return;
		}
	    }
	}
    	    
    	
    	

	  public void addVar(String x) {

	       scopes.getFirst().put(x,new Value.Undefined());
	  }
	  public void addFun(String x,Def d){
	  	if(signature.get(x)!=null)
	  	  throw new RuntimeException("function "+x+ " already exists ");
	  	else
	  	  signature.put(x,d);  
	  	
	  	}

	   public void enterScope() {
	     scopes.addFirst(new HashMap<String,Value>());
    	 }

	    public void leaveScope() {
	    scopes.removeFirst();
	  }
   }	
    
	public void interpret(Program p) {
		   PDefs program=(PDefs)p;
		   Env   environment=new Env();
		   boolean  tag_main=false;
		   for(Def d: program.listdef_){ 
		   	  environment.addFun(((DFun)d).id_,d);   
		   }
		   for(Def d: program.listdef_){ 
			       if(((DFun)d).id_.equals("main")){
			    	  tag_main=true;
			          break;
			       }
			       
			   }
		    if(!tag_main) return;
		    Def entrance=environment.lookupFun("main");
		    if(entrance==null){
		       throw new RuntimeException("can't find function main");	
		    	}	
		    else{
		    	 DFun df=(DFun)entrance;
		    	 environment.enterScope(); 
		    	 for(Stm x:df.liststm_){
		    	 	 execStm(x,environment);
		    	 	 if(x instanceof SReturn)
		    	 	    return ;
		    	 	 
		    	 	}                
		    	}
		    }
	private Value execStm(Stm s,Env environment){
		   
		     return s.accept(new stmExecutor(),environment);
		     
		} 	   
  private class stmExecutor implements Stm.Visitor<Value,Env>{
	 	public Value visit(CPP.Absyn.SExp p, Env environment)
    {
          evalExp(p.exp_,environment);
         
          return null;
    }
    public Value visit(CPP.Absyn.SDecls p, Env environment)
    {
        for (String x : p.listid_) {
          environment.addVar(x);
      }

      return null;
    }
    public Value visit(CPP.Absyn.SInit p, Env environment)
    {  
    	       environment.addVar(p.id_);
    	       environment.setVar(p.id_,evalExp(p.exp_,environment));
    	       
    	       return null;
    }
    public Value visit(CPP.Absyn.SReturn p, Env environment)
    {
             return evalExp(p.exp_,environment);
    }
    public Value visit(CPP.Absyn.SWhile p,Env environment)
    {       
    	      Value v=evalExp(p.exp_,environment);
              Value ret=null;
            if(v.getBool()){
            	  if(p.stm_ instanceof SReturn){
            	    ret=execStm(p.stm_,environment);
            	    return ret;
            	  }
            	  else{
            	      ret=execStm(p.stm_,environment);
            		  execStm(p,environment);          
            	  }
            	  }
          return ret;
    }
    public Value visit(CPP.Absyn.SBlock p, Env environment)
    {
         environment.enterScope();
         Value ret=null;
        for (Stm x : p.liststm_) {
        	 ret=execStm(x,environment);
               if(x instanceof SReturn){
           	break;	
           }
         }
    
        environment.leaveScope();
        return ret;
    }
    public Value visit(CPP.Absyn.SIfElse p, Env environment)
    {
    	   
    	   Value ret=null;
    	   Boolean b=evalExp(p.exp_,environment).getBool();
    	   
         if(b){
            
         	   ret=execStm(p.stm_1,environment);
         	}   
         	else{
         	   	ret=execStm(p.stm_2,environment);
         		 
                  
         	}
       return ret;
    }
 }
  private Value evalExp(Exp e,Env environment){
  	       return e.accept(new expEvaluator(),environment);
  	}
  private class expEvaluator implements Exp.Visitor<Value,Env>{
  	    public Value visit(CPP.Absyn.ETrue p, Env environment)
        
    {
       return  new Value.BoolValue(true);
    }
    public Value visit(CPP.Absyn.EFalse p,Env environment)
    {
    	 return new Value.BoolValue(false);
    }
    public Value visit(CPP.Absyn.EInt p,Env environment)
    {
       return  new Value.IntValue(p.integer_);
    }
    public Value visit(CPP.Absyn.EDouble p,Env environment)
    { 
    	  return new Value.DoubleValue(p.double_);
    }
    public Value visit(CPP.Absyn.EId p,Env environment)
    {
       
      return environment.lookupVar(p.id_);
    }
    public Value visit(CPP.Absyn.EApp p, Env environment)
    { 
    	  Value ve;  
    	 if(p.id_.equals("printInt")){
    	 	
    	 	
    	 	  for(Exp e:p.listexp_){  
    	 	    ve=evalExp(e,environment);
    	 	    if(!(ve.myType().equals("integer")))
    	 	      throw new RuntimeException("the argumetn of printInt must be integer");
    	 	    else {
                          System.out.println(ve.getInt());
    	 	    	 return null;
    	 	    	}
    	 	    }
    	 	}
    	 	
    	  else if(p.id_.equals("printDouble"))	{
    	 	   	  for(Exp e:p.listexp_){  
    	 	   	  ve=evalExp(e,environment);	
    	 	    if(!(ve.myType().equals("double")))
    	 	      throw new RuntimeException("the argumetn of printInt must be double");
    	 	    else {
    	 	    	 System.out.println(ve.getDouble());
    	 	    	 return null;
    	 	    	}
    	 	    }
    	 	} 
    	  else if(p.id_.equals("readInt"))	{
    	  	     
                     int v = scan.nextInt();
                        
                     return new Value.IntValue(v);
    	 	} 
    	 	 else if(p.id_.equals("readDouble"))	{
    	 	      
                       double v = scan.nextDouble();
                       
    	 	       return new Value.DoubleValue(v);
    	 	} 
    	 else{
           Def d=environment.lookupFun(p.id_);
           DFun df=(DFun)d;
            LinkedList<Value>  value_list=new LinkedList<Value>();
              for(Exp e:p.listexp_){
       	      value_list.add(evalExp(e,environment));
            	} 
            environment.enterScope();
  
          for(int i=0;i<value_list.size();i++){
       	      ADecl ad=(ADecl)df.listarg_.get(i);
       	      environment.addVar(ad.id_);
       	      environment.setVar(ad.id_,value_list.get(i));
          	}
            
           Value v=null;
       
           for (Stm x : df.liststm_) {
              v=(Value)execStm(x,environment); 
              if(x instanceof SReturn) 
               break ;
          } 
                              
         environment.leaveScope();	           	
         return v;
     } 
        return null;
    }
    public Value visit(CPP.Absyn.EPIncr p,Env environment)
    {
           Value v=evalExp(p.exp_,environment);
           String x=((EId)p.exp_).id_;
           if(v.myType().equals("integer"))
           {
             int i=v.getInt();
             environment.setVar(x,new Value.IntValue(i+1));
          
           } 
           else{
           	 double i=v.getDouble();
           	 environment.setVar(x,new Value.DoubleValue(i+1.0));
       
           	}
           	return v;
           
    }
    public Value visit(CPP.Absyn.EPDecr p, Env environment)
    {
           Value v=evalExp(p.exp_,environment);
           String x=((EId)p.exp_).id_;
           if(v.myType().equals("integer")){
           	  int i=v.getInt();
           	  environment.setVar(x,new Value.IntValue(i-1));
           	
           	}
           	else{
           		double i=v.getDouble();
           		environment.setVar(x,new Value.DoubleValue(i-1.0));
           		}
           return v;
    }
    public Value visit(CPP.Absyn.EIncr p, Env environment)
    {     
    	     Value v=evalExp(p.exp_,environment);
    	     String x=((EId)p.exp_).id_;
    	     v.increase();
           environment.setVar(x,v);
           return v;
    }
    public Value visit(CPP.Absyn.EDecr p, Env environment)
    {     
    	     Value v=evalExp(p.exp_,environment);
    	     String x=((EId)p.exp_).id_;
    	     v.decrease();
           environment.setVar(x,v);
           
           return v;
    }
    public Value visit(CPP.Absyn.ETimes p, Env environment)
    {
           Value  v1=evalExp(p.exp_1,environment);
           Value  v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
               return new Value.IntValue(v1.getInt()*v2.getInt());
              
           }
           
           else 
             return new Value.DoubleValue(v1.getDouble()*v2.getDouble());
     

    }
    public Value visit(CPP.Absyn.EDiv p,Env environment)
    {
    	     
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           
           if(v1.myType().equals("integer")){
              if(v2.getInt()!=0) 
               return new Value.IntValue(v1.getInt()/v2.getInt());
              else
               throw new RuntimeException("divider should not be zero");
           }
           else{
              if(v2.getDouble()!=0.0)
              return new Value.DoubleValue(v2.getDouble()/v2.getDouble());
              else
              throw new RuntimeException("divider should not be zero");
              }
    }
    public Value visit(CPP.Absyn.EPlus p,Env environment)
    {   
    	     Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
                
              return new Value.IntValue(v1.getInt()+v2.getInt());
             
           }
           
           else 
             return new Value.DoubleValue(v1.getDouble()+v2.getDouble());
     
           
    }
    public Value visit(CPP.Absyn.EMinus p,Env environment)
    {
    	
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
              return new Value.IntValue(v1.getInt()-v2.getInt());
             
           }
           
           else 
             return new Value.DoubleValue(v1.getDouble()-v2.getDouble());
     
    }
    public Value visit(CPP.Absyn.ELt p,Env environment)
    {
    	    
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
              int i=v1.getInt().intValue();
              int j=v2.getInt().intValue();
              return new Value.BoolValue(i<j);
             
           }
           
           else {
        	   double i=v1.getDouble().doubleValue();
               double j=v2.getDouble().doubleValue();
              return new Value.BoolValue(i<j);
           }
     }
    public Value visit(CPP.Absyn.EGt p, Env environment)
    {
    	    
          
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
               int i=v1.getInt().intValue();
               int j=v2.getInt().intValue();
               return new Value.BoolValue(i>j);
              
            }
            
            else {
         	   double i=v1.getDouble().doubleValue();
                double j=v2.getDouble().doubleValue();
               return new Value.BoolValue(i>j);
            }
    }
    public Value visit(CPP.Absyn.ELtEq p, Env environment)
    {
    	     
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
               int i=v1.getInt().intValue();
               int j=v2.getInt().intValue();
               return new Value.BoolValue(i<=j);
              
            }
            
            else {
         	   double i=v1.getDouble().doubleValue();
                double j=v2.getDouble().doubleValue();
               return new Value.BoolValue(i<=j);
            }
    }
    public Value visit(CPP.Absyn.EGtWq p, Env environment)
    {
    	  
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
               int i=v1.getInt().intValue();
               int j=v2.getInt().intValue();
               return new Value.BoolValue(i>=j);
              
            }
            
            else {
         	   double i=v1.getDouble().doubleValue();
                double j=v2.getDouble().doubleValue();
               return new Value.BoolValue(i>=j);
            }
    }
    public Value visit(CPP.Absyn.EEq p, Env environment)
    {
        
            
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
               int i=v1.getInt().intValue();
               int j=v2.getInt().intValue();
               return new Value.BoolValue(i==j);
              
            }
            
            else {
         	   double i=v1.getDouble().doubleValue();
                double j=v2.getDouble().doubleValue();
               return new Value.BoolValue(i==j);
            }
    }
    public Value visit(CPP.Absyn.ENEq p,Env environment)
    {
     
           Value v1=evalExp(p.exp_1,environment);
           Value v2=evalExp(p.exp_2,environment);
           if(v1.myType().equals("integer")){
               int i=v1.getInt().intValue();
               int j=v2.getInt().intValue();
               
               return new Value.BoolValue(i!=j);
              
            }
            
            else {
         	   double i=v1.getDouble().doubleValue();
                  double j=v2.getDouble().doubleValue();
      
               return new Value.BoolValue(i!=j);
            }
    }
    public Value visit(CPP.Absyn.EAnd p, Env environment)
    {
           Value v1=evalExp(p.exp_1,environment);
           if(v1.getBool()){
           	  Value v2=evalExp(p.exp_2,environment);
           	  if(v2.getBool())
           	    return new Value.BoolValue(true);
           	    else
           	    return new Value.BoolValue(false); 
           	}
           	else
           	  return new Value.BoolValue(false);
 
    }
    public Value visit(CPP.Absyn.EOr p,Env environment)
    {
    	     Value v1=evalExp(p.exp_1,environment);
           if(!v1.getBool()){
           	  Value v2=evalExp(p.exp_2,environment);
           	  if(!v2.getBool())
           	    return new Value.BoolValue(false);
           	    else
           	    return new Value.BoolValue(true); 
           	}
           	else
           	  return new Value.BoolValue(true);
 
    }
    public Value visit(CPP.Absyn.EAss p, Env environment)
    {
    	       Value v2=evalExp(p.exp_2,environment);
    	       String x=((EId)p.exp_1).id_; 
    		      
    	       environment.setVar(x,v2);
               return v2;
    }
	 	
	 	}
  	
  
  
  }
 

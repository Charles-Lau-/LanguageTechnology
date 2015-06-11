import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;

 
import CPP.Absyn.*;
public class Compiler {
	public String fileName="";
	public static String fileName_stat;
	private Env environment=new Env();
	public FileWriter fileWriter;
	public static enum Label {TEST {public String toString() {return "TEST";}},
		                      END {public String toString() {return "END";}},
		                      TRUE {public String toString() {return "TRUE";}},
		                      FALSE{public String toString(){return "FALSE";}}}	
    private static class NewLabel{

    	  private int test_counter;
    	  private int end_counter;
    	  private int true_counter;
    	  private int false_counter;
    	 
    	  public String getLabel(String s){
    		   if(s.equals("TEST"))
    			    
    			    return Label.TEST.toString()+(++test_counter)+":";
    		   
    		   else if(s.equals("END"))
    			    return Label.END.toString()+(++end_counter)+":";
    		   else if(s.equals("TRUE"))
    			   return Label.TRUE.toString()+(++true_counter)+":";
    		   else
    			   return Label.FALSE.toString()+(++false_counter)+":";
    	  } 
    }            
    public static class FunType {
        public LinkedList<Type> args ;
        public Type val ;
        public FunType(Type val,LinkedList<Type> args){
        	   
        	   this.args=args;
        	   this.val=val;
        	 
        	}
        public FunType(Type val){
       	 
       	 
       	 this.args=null;
       	 this.val=val;
        }
        }
    private static class Env{
    	private LinkedList<HashMap<String,Integer>> scopes;
        private LinkedList<NewLabel> Labels;
        private HashMap<String,FunType> signature;
        private TypeChecker.TypeCode tt;
        private Integer maxvar;
        
    	public Env() {
    	    this.scopes = new LinkedList<HashMap<String,Integer>>();
            this.maxvar = 0 ;
            this.Labels=new LinkedList<NewLabel>();     
            this.signature=new HashMap<String,FunType>();
        	
    	}
    	public Integer lookupVar(String x) {
    	    for (HashMap<String,Integer> scope : scopes) {
    		Integer v = scope.get(x);
    		if (v != null)
    		    return v;
    	    }
    	    throw new RuntimeException("Unknown variable " + x + " in " + scopes);
    	}
    	public FunType lookupFun(String fun){
     	   FunType ft=signature.get(fun);
     	   if(ft!=null)
     	     return ft;
     	   else
     	     throw new TypeException("Unknown function  "+fun);
     	 } 
    	 public void addFun(String x,FunType ft){
    		  	if(signature.get(x)!=null)
    		  	  throw new TypeException("function "+x+ " already exists ");
    		  	else
    		  	  signature.put(x,ft);  
    		  	
    	
        		
    		  	}
    	public void addVar(String x, Type t) {
    	    scopes.getFirst().put(x,maxvar);
                maxvar++;
    	    if (t instanceof Type_double) maxvar++ ;   
    	}
    	public void enterScope() {
    	    scopes.addFirst(new HashMap<String,Integer>());
     	}
        public NewLabel getNewLabel(){
        	  return  Labels.getFirst();
        }
    	public void leaveScope() {
    	        HashMap<String,Integer> hm=scopes.getFirst();
    	        int offset=1000;
    	        for(int i:hm.values()){
    	        	   if(i<offset)
    	        		   offset=i;
    	        }
    	        maxvar=offset;
    	        scopes.removeFirst();
    	      
    	}
    	public void enterFunction(){
    		Labels.addFirst(new NewLabel());
    	}
    	public void leaveFunction(){
    		Labels.removeFirst();
    	}
    	public void set_this_function(TypeChecker.TypeCode t){
    		 
    		    	  tt=t;
    	}
    	public TypeChecker.TypeCode lookupCurrentFun(){
    		     return tt;
    	} 
    	
    }
    private void emit(String intruction){
    	  try {
  			fileWriter.write(intruction+"\r\n");
  		} catch (IOException e) {
  			// TODO Auto-generated catch block
  			e.printStackTrace();
  		}
			
    }
	public void compile(Program p,String fn) throws IOException{
		  this.fileName=fn;
	      fileName_stat=fn;
	      File f=new File(fn+".j");  
	      fileWriter=new FileWriter(f);
	       
	      PDefs program=(PDefs)p;
			  
		  for(Def d: program.listdef_){
		  	    LinkedList<Type> argType_List=new LinkedList<Type>();
		  	    DFun df=(DFun)d;
		  	    for(Arg g:df.listarg_){
		  	    	  ADecl ad=(ADecl)g;
		  	    	  argType_List.addLast(ad.type_); 
		  	    	}
		  	     
		  	     FunType ft=new FunType(df.type_,argType_List);
		  	     environment.addFun(df.id_,ft);   
		  	}  
		  
		    emit(".class public "+this.fileName) ;  
		    emit(".super java/lang/Object") ;
		    emit("") ;
		    emit(".method public <init>()V") ;
		    emit("aload_0") ;
		    emit("invokenonvirtual java/lang/Object/<init>()V") ;
		    emit("return") ;
		    emit(".end method") ;
		    emit("") ;
		    
		    
		    for(Def d:program.listdef_){
		    	 environment.enterScope();
		    	 environment.enterFunction();
		         compileDef(d,null);
		         environment.leaveFunction();
		         environment.leaveScope();
		    }
		    fileWriter.flush();
		    fileWriter.close();
		    Generater.generate_class(f);
		             	
			
   }
	private void compileDef(Def d,Object o){
		         d.accept(new defCompiler(), o);
	}
	private class defCompiler implements Def.Visitor<Object,Object>{
	  	public Def visit(CPP.Absyn.DFun d, Object o){
	  	  
		        
	  		  if(d.id_.equals("main")){
	  		     environment.set_this_function(TypeChecker.TypeCode.CVoid);
	 	  			 
	  		     environment.addVar("args",null);
	  		    	
	  		    	 
	  		     emit(".method public static main([Ljava/lang/String;)V") ;
	  			 emit(".limit locals 100") ; //bogus limit
	  			 emit(".limit stack 1000") ; //bogus limit
	  		     for(Stm s:d.liststm_){
	  		    	 compileStm(s,environment);
	  		     }
	  		 	 emit("return");  
	  		     emit(".end method");
	  		     } 
	  		     else{
	  		        if(d.type_ instanceof Type_double)
	  		        	environment.set_this_function(TypeChecker.TypeCode.CDouble);
	  		        else if(d.type_ instanceof Type_void)
	  		        	environment.set_this_function(TypeChecker.TypeCode.CVoid);
	  		        else
                        environment.set_this_function(TypeChecker.TypeCode.CInt);
	  		       
	  		    	StringBuffer sinagture=new StringBuffer(); 
	  	           for(Arg a:d.listarg_){
	  	        	     ADecl ad=(ADecl)a;
	  	        	     environment.addVar(ad.id_, ad.type_);
		            	 if(ad.type_  instanceof Type_int)
		            		 sinagture.append("I");
		  		    		else if(ad.type_  instanceof Type_double)
		  		    			 sinagture.append("B");
		 		  		    	else if(ad.type_ instanceof Type_bool)
		 		  		    	 sinagture.append("Z");
		             }
		    
		          	if(d.type_ instanceof Type_int)
		          		 sinagture.append("I");
			  		    	
	  		    	else if(d.type_  instanceof Type_double)
	  		    		 sinagture.append("B");
			  		    	
		    		else if(d.type_ instanceof Type_bool)
		    			 sinagture.append("Z");
		  		    	
		    		else
		    			 sinagture.append("V");
		  		    	
		           
		  		  
		            int l=sinagture.length();
		          	if(!(l>1))
		           emit(".method public static  "+d.id_+"("
		    			 +")"+
		            	sinagture.charAt(sinagture.length()-1));
		          	else{
		          		String s=""+sinagture.charAt(l-1);
		          		emit (".method public static  "+d.id_+"("
		  		    			 +sinagture.deleteCharAt(l-1)+")"+
				            	s);
		          	}
	  		      
	  		  		  
	  		        emit(".limit locals 100");
	  		    	emit(".limit stack 1000");
	  		     	for(Stm s:d.liststm_){
	  		    		compileStm(s,environment);
	  		    		
	  		    	}
	  	  		 	 emit("return");  
	  	  			
	  		       	emit(".end method");
	  		     }
	  		     return null;
	  	}
	    		
	}
	 private void compileStm(Stm s,Object o){
		         s.accept(new stmCompiler(), o);
	 }
	  private class stmCompiler implements Stm.Visitor<Object,Object>{
		public Object visit(CPP.Absyn.SExp p, Object o )
	    {
			   AnnoType at=(AnnoType)p.exp_;
			   compileExp(at.exp_,at.type_); 
		        
			   
			   
	          if(at.type_ instanceof Type_double){
               	emit("pop2");
                    }
                 else if(at.type_ instanceof Type_void) {
               	  
                     }
                 else
                	 emit("pop");
	           return null;
	    }
	    public Object visit(CPP.Absyn.SDecls p, Object o)
	    {
			 		
	        for (String x : p.listid_) {
	          environment.addVar(x,p.type_);
	      }

	      return null;
	    }
	  
		public Object visit(CPP.Absyn.SInit p, Object o)
	    {  
			   AnnoType at=(AnnoType)p.exp_;
			   environment.addVar(p.id_, p.type_);
			     
			    compileExp(at.exp_,at.type_);
	    	     
		        	  
			    int id=environment.lookupVar(p.id_);
	    	       
			    if(p.type_ instanceof Type_double){
	    	    	   
	    	    	   emit("dstore "+id);
	    	       }
	    	       else {
	    	    	   emit("istore "+id);
	    	       }
	    	       
	    	       return null;
	    }
	    public Object visit(CPP.Absyn.SReturn p, Object o)
	    {
                      
	    	          TypeChecker.TypeCode this_function=environment.lookupCurrentFun(); 
			          AnnoType at=(AnnoType)p.exp_;
				 
	                  compileExp(at.exp_,at.type_);
	                  
	                  if(this_function == TypeChecker.TypeCode.CDouble){
	                    	emit("dreturn");
	                  }
	                  else if(this_function == TypeChecker.TypeCode.CVoid){
	                	    emit("return");
	                  }
	                  else  {
	                       emit("ireturn");
	                   }
	                  return null; 
	    }
	    public Object visit(CPP.Absyn.SWhile p,Object o)
	    {       

			   AnnoType at=(AnnoType)p.exp_;
				
	    	    NewLabel l=environment.getNewLabel();
	    	    String t_label=l.getLabel("TEST");
	    	    String e_label=l.getLabel("END");
	    	    emit(t_label);
	    	    
	    	    compileExp(at.exp_,at.type_);
	    	    emit("ifeq "+e_label.split(":")[0]);
	            compileStm(p.stm_,environment);
	            emit("goto "+t_label.split(":")[0]);
	            emit(e_label);
	          
	            return null;
	    }
	    public Object visit(CPP.Absyn.SBlock p, Object o)
	    {
	         environment.enterScope();
	        for (Stm x : p.liststm_) {
	        	 compileStm(x,environment);
	            }
	        environment.leaveScope();
	        return null;
	    }
	    public Object visit(CPP.Absyn.SIfElse p, Object o)
	    {

			   AnnoType at=(AnnoType)p.exp_;
				
	        NewLabel l=environment.getNewLabel();
	       
	    	compileExp(at.exp_,at.type_);
	    	 String  f_label=l.getLabel("fALSE");
		     String  t_label=l.getLabel("TRUE");
	    	emit("ifeq "+f_label.split(":")[0]);
	    	compileStm(p.stm_1,o);
	    	emit("goto "+t_label.split(":")[0]);
            emit(f_label);
            compileStm(p.stm_2,o);
        
			
            emit(t_label);
             
            return null;
	    }
	  }
	  
	  private void compileExp(Exp e,Type t){
		  
		    e.accept(new expCompiler(), t);
	  }
	  private class expCompiler implements Exp.Visitor<Object, Type>{
		  public Object visit(CPP.Absyn.ETrue p, Type t)
		    {
			         emit("bipush 1");
		             return null;
		    }
		    public Object visit(CPP.Absyn.EFalse p,Type t)
		    {
		    	     emit("bipush 0");
		    	     return null;
		    }
		    public Object visit(CPP.Absyn.EInt p,Type t)
		    {
		    	 emit("ldc "+p.integer_);
		       return  null;
		    }
		    public Object visit(CPP.Absyn.EDouble p,Type t)
		    { 
		    	  emit("ldc2_w "+p.double_);
		    	 return null;
		    }
		    public Object visit(CPP.Absyn.EId p,Type t)
		    {     
		    	  
		          int address=environment.lookupVar(p.id_);
		          if(t instanceof Type_double)
		                 emit("dload "+address);
		          else 
		        	    emit("iload "+address);
		      
		          return null;
		    }
		    public Object visit(CPP.Absyn.EApp p,Type t)
		    { 
		         
		        
		    	  
		    	 if(p.id_.equals("printInt")){
		    		  for(Exp e:p.listexp_){
		            	  AnnoType at=(AnnoType)e;
		                   compileExp(at.exp_,at.type_);	 
		             }   
		    	 	   emit("invokestatic Runtime/printInt(I)V");
		    	 	}
		    	 	
		    	  else if(p.id_.equals("printDouble"))	{
		    		  for(Exp e:p.listexp_){
		            	  AnnoType at=(AnnoType)e;
		                   compileExp(at.exp_,at.type_);	 
		             }   
		    	 	   emit("invokestatic Runtime/printDouble(D)V");
		    	 	} 
		    	  else if(p.id_.equals("readInt"))	{
		    		  for(Exp e:p.listexp_){
		            	  AnnoType at=(AnnoType)e;
		                   compileExp(at.exp_,at.type_);	 
		             }   
		    	  	   emit("invokestatic Runtime/readInt()I"); 
		    	 	} 
		    	 	 else if(p.id_.equals("readDouble"))	{
		    	 		  for(Exp e:p.listexp_){
			            	  AnnoType at=(AnnoType)e;
			                   compileExp(at.exp_,at.type_);	 
			             }   
		    	 	   emit("invokestatic Runtime/readDouble()D");
		    	 	} 
		    	 else{
		             for(Exp e:p.listexp_){
		            	  AnnoType at=(AnnoType)e;
		                   compileExp(at.exp_,at.type_);	 
		             }   
		              
		              FunType ft=environment.lookupFun(p.id_);
                       StringBuffer sinagture=new StringBuffer();
                      
		             for(Type da:ft.args){
		            	 if(da  instanceof Type_int)
		            		 sinagture.append("I");
		  		    		else if(da  instanceof Type_double)
		  		    			 sinagture.append("B");
		 		  		    	else if(da instanceof Type_bool)
		 		  		    	 sinagture.append("Z");
		             }
		    
		          	if(ft.val instanceof Type_int)
		          		 sinagture.append("I");
			  		    	
	  		    	else if(ft.val  instanceof Type_double)
	  		    		 sinagture.append("B");
			  		    	
  		    		else if(ft.val instanceof Type_bool)
  		    			 sinagture.append("Z");
 		  		    	
  		    		else
  		    			 sinagture.append("V");
 		  		    	
		           
		  		  
		            int l=sinagture.length();
		          	if(!(l>1))
		           emit("invokestatic "+fileName_stat+"/"+p.id_+"("
  		    			 +")"+
		            	sinagture.charAt(sinagture.length()-1));
		          	else{
		          		String s=""+sinagture.charAt(l-1);
		          		emit ("invokestatic "+fileName_stat+"/"+p.id_+"("
		  		    			 +sinagture.deleteCharAt(l-1)+")"+
				            	s);
		          	}
		    	 } 
		    	 
		    		 return null;
		    }
		    public Object visit(CPP.Absyn.EPIncr p,Type t)
		    {
 
		    	 int address=environment.lookupVar(((EId)p.exp_).id_);
			     compileExp(p.exp_, t);
		         if(t instanceof Type_double){
		        	  emit("dload "+address);
		        	  emit("ldc2_w "+"1.0");
		        	  emit("dadd");
		        	  emit("dstore "+address); 
		         } 
		         else
		        	 emit("iinc "+address+" "+"1");
		           		    	  
		    	  return null;
		         
		    }
		    public Object visit(CPP.Absyn.EPDecr p, Type t)
		    {
		       	   
		         int address=environment.lookupVar(((EId)p.exp_).id_);
			     compileExp(p.exp_, t);
		         if(t instanceof Type_double){
		       	     emit("dload "+address);
				    
		        	  emit("ldc2_w "+"-1.0");
		        	  emit("dadd");
		        	  emit("dstore "+address); 
		         } 
		         else
		    	    emit("iinc "+environment.lookupVar(((EId)p.exp_).id_)+" "+"-1");
			           
		    	  
		             return null;
		    }
		    public Object visit(CPP.Absyn.EIncr p, Type t)
		    {     
		 	   
		         int address=environment.lookupVar(((EId)p.exp_).id_);
			     if(t instanceof Type_double){
			    	  emit("dload "+address);
		        	  emit("ldc2_w "+"1.0");
		        	  emit("dadd");
		        	  emit("dstore "+address); 
		         } 
		    	  emit("iinc "+environment.lookupVar(((EId)p.exp_).id_)+" "+"1");
		          compileExp(p.exp_, t);    
		            return null;
		    }
		    public Object visit(CPP.Absyn.EDecr p, Type t)
		    {     
		    	 int address=environment.lookupVar(((EId)p.exp_).id_);
			     if(t instanceof Type_double){
			    	  emit("dload "+address);
		        	  emit("ldc2_w "+"-1.0");
		        	  emit("dadd");
		        	  emit("dstore "+address); 
		         } 
		    	  emit("iinc "+environment.lookupVar(((EId)p.exp_).id_)+" "+"-1");
		          compileExp(p.exp_, t);
		          
			      return null;
		    }
		    public Object visit(CPP.Absyn.ETimes p, Type t)
		    {
		    	 AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           
		           if(t instanceof Type_int){
		        	   emit("imul");
		           }
		           else
		        	   emit("dmul"); 
		           
		           
		           return null;

		    }
		    public Object visit(CPP.Absyn.EDiv p,Type t)
		    {
		    	     
		    	 AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           
		           if(t instanceof Type_int){
		        	   emit("idiv");
		           }
		           else
		        	   emit("ddiv"); 
		           
		           
		           return null;

		    }
		    public Object visit(CPP.Absyn.EPlus p,Type t)
		    {   
		    	 AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
	           
	           if(t instanceof Type_int){
	        	   emit("iadd");
	           }
	           else
	        	   emit("dadd"); 
	           
	           
	           return null;
		           
		    }
		    public Object visit(CPP.Absyn.EMinus p,Type t)
		    {
		        	
		     	 AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           
		    	 if(t instanceof Type_int){
		        	   emit("isub");
		           }
		           else
		        	   emit("dsub"); 
		           
		           
		           return null;
		     
		    }
		    public Object visit(CPP.Absyn.ELt p,Type t)
		    {        
		    	     String t_label=environment.getNewLabel().getLabel("TRUE");
		    	     emit("bipush 1");
		    	      
		    	       AnnoType at1=(AnnoType)p.exp_1;
			    	   AnnoType at2=(AnnoType)p.exp_2;
			           compileExp(at1.exp_,at1.type_);
			           compileExp(at2.exp_,at2.type_);
		    	     if(at2.type_ instanceof Type_double | at1.type_ instanceof Type_double){
		    	               	  emit("dcmpl");
		    	               	  
		    	               	  emit("ldc 0");
		    	               	  emit("if_icmpgt "+t_label.split(":")[0]);
		    	       }
		    	     else{ 
		    	    	 emit("if_icmplt "+t_label.split(":")[0]);
		    	     }
		    	     emit("pop");
		    	     emit("bipush 0");
		    	     emit(t_label);
		             return null;
		     }
		    public Object visit(CPP.Absyn.EGt p, Type t)
		    {
		    	    
		          
		    	 String t_label=environment.getNewLabel().getLabel("TRUE");
	    	     emit("bipush 1");
	    	     AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           if(at2.type_ instanceof Type_double | at1.type_ instanceof Type_double){
 	               	  emit("dcmpg");
 	               	  
 	               	  emit("ldc 0");
 	               	  emit("if_icmpgt "+t_label.split(":")[0]);
 	       }
 	       else{ 
 	               emit("if_icmpgt "+t_label.split(":")[0]);
	    	}
	    	     emit("pop");
	    	     emit("bipush 0");
	    	     emit(t_label);
	             return null;
		    }
		    public Object visit(CPP.Absyn.ELtEq p, Type t)
		    {
		    	     
		    	 String t_label=environment.getNewLabel().getLabel("TRUE");
	    	     emit("bipush 1");
	    	     AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           if(at2.type_ instanceof Type_double | at1.type_ instanceof Type_double){
		        	        emit("dcmpg");
		        	        emit("ldc 1");
		        	        emit("if_icmplt "+t_label.split(":")[0]);
	 	               	
		           }
		         else{
	    	     emit("if_icmple "+t_label.split(":")[0]);
		         }
	    	     emit("pop");
	    	     emit("bipush 0");
	    	     emit(t_label);
	             return null;
		    }
		    public Object visit(CPP.Absyn.EGtWq p, Type t)
		    {
		    	  
		    	 String t_label=environment.getNewLabel().getLabel("TRUE");
	    	     emit("bipush 1");
	    	     AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           if(at2.type_ instanceof Type_double | at1.type_ instanceof Type_double){
	        	        emit("dcmpl");
	        	        emit("ldc 1");
	        	        emit("if_icmplt "+t_label.split(":")[0]);
	               	
	           }
	         else{
	               emit("if_icmpge "+t_label.split(":")[0]);
	     	      }  
	    	     emit("pop");
	    	     emit("bipush 0");
	    	     emit(t_label);
	             return null;
		    }
		    public Object visit(CPP.Absyn.EEq p, Type t)
		    {
		        
		            
		    	 String t_label=environment.getNewLabel().getLabel("TRUE");
	    	     emit("bipush 1");
	    	     AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		         
		    	  compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           if(at2.type_ instanceof Type_double | at1.type_ instanceof Type_double)
		        	   {
		        		   emit("dcmpl");
		        		   emit("ifeq "+t_label.split(":")[0]);
		        	   }
		        		   
		        	      
		        	   
		        	   else{      
		         emit("if_icmpeq "+t_label.split(":")[0]);
		        	   }
		         emit("pop");
	    	     emit("bipush 0");
	    	     emit(t_label);
	             return null;
		    }
		    public Object visit(CPP.Absyn.ENEq p,Type t)
		    {
		    	 String t_label=environment.getNewLabel().getLabel("TRUE");
	    	     emit("bipush 1");
	    	     AnnoType at1=(AnnoType)p.exp_1;
		    	 AnnoType at2=(AnnoType)p.exp_2;
		           compileExp(at1.exp_,at1.type_);
		           compileExp(at2.exp_,at2.type_);
		           if(at2.type_ instanceof Type_double | at1.type_ instanceof Type_double)
		        	   {
		        		       emit("dcmpl"); 
		        		       emit("ifne "+t_label.split(":")[0]);
		        	   }
		        	   else
		        	   {
	    	     emit("if_icmpne "+t_label.split(":")[0]);
		        	   }
	    	     emit("pop");
	    	     emit("bipush 0");
	    	 	 emit(t_label);
	             return null;
		    }
		    public Object visit(CPP.Absyn.EAnd p, Type t)
		    {
		    	    String t_label=environment.getNewLabel().getLabel("TRUE");
		    	    String f_label=environment.getNewLabel().getLabel("FALSE");
		    	    AnnoType at1=(AnnoType)p.exp_1;
			    	 
			           compileExp(at1.exp_,at1.type_);
			          emit("ifeq "+f_label.split(":")[0]);
			    
			    	 AnnoType at2=(AnnoType)p.exp_2;
			        
			           compileExp(at2.exp_,at2.type_);
		            emit("ifeq "+f_label.split(":")[0]);
		            emit("bipush 1");
		            emit("goto "+t_label.split(":")[0]);
		            emit(f_label);
		            emit("bipush 0");
		            emit(t_label);
		            return null;
		    }
		    public Object visit(CPP.Absyn.EOr p,Type t)
		    {
		    	    String t_label=environment.getNewLabel().getLabel("TRUE");
		    	    String f_label=environment.getNewLabel().getLabel("FALSE");
		            
		    	    AnnoType at1=(AnnoType)p.exp_1;
			           compileExp(at1.exp_,at1.type_);
			            emit("ifne "+f_label.split(":")[0]);
			       	 AnnoType at2=(AnnoType)p.exp_2;
					 compileExp(at2.exp_,at2.type_);    
					emit("ifne "+f_label.split(":")[0]);
		            emit("bipush 0");
		            emit("goto "+t_label.split(":")[0]);
		            emit(f_label);
		            emit("bipush 1");
		            emit(t_label);
		            return null;
		 
		    }
		    public Object visit(CPP.Absyn.EAss p, Type t)
		    { 
		    	   AnnoType at1=(AnnoType)p.exp_1;
			    	 AnnoType at2=(AnnoType)p.exp_2;
			             compileExp(at2.exp_,at2.type_);
		            int address=environment.lookupVar(((EId)at1.exp_).id_);
		             if(at2.type_ instanceof Type_double){
		            	  emit("dup2");
		            	  emit("dstore "+address);
		             }
		            else{
		                   emit("dup");
		            	   emit("istore "+address);
		            } 
		            return null;
		    }
		 		public Object visit(AnnoType p, Type t) {
		           p.exp_.accept(new expCompiler(),t);
				  return null;
			}
			 	
			 	}
		  	
		  
		  
		  
	  
}

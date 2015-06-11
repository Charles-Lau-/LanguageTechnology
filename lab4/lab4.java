import CPP.*;
import java.io.*;
 

public class lab4 {
	public static void main(String args[]) {
	   	if (args.length < 1) {
			System.err.println("Usage: lab4 <SourceFile>");
			System.exit(1);	
		}
                String flag="";
                if(args.length==1)
                      flag="-v";
                else
                      flag=args[0];       
		Yylex l = null;
		try { 
                       if(args.length==1) 
		        l = new Yylex(new FileReader(args[0]));
                       else
                        l = new Yylex(new FileReader(args[1]));
                     
			parser p = new parser(l);
	 
			CPP.Absyn.Program parse_tree = p.pProgram();
		        
                        new Interpreter().interpret(parse_tree,flag);
	 
		}  catch (TypeException e) {
			System.out.println("TYPE ERROR");
			System.err.println(e.toString());
			System.exit(1);
		} catch (RuntimeException e) {
		    //			System.out.println("RUNTIME ERROR");
			System.err.println(e.toString());
			System.exit(-1);
		} catch (IOException e) {
			System.err.println(e.toString());
			System.exit(1);
		} catch (Throwable e) {
			System.out.println("SYNTAX ERROR");
			System.out.println("At line " + String.valueOf(l.line_num()) 
					   + ", near \"" + l.buff() + "\" :");
			System.out.println("     " + e.getMessage());
			e.printStackTrace();
			System.exit(1);
		}
	}
}

import CPP.*;
import java.io.*;

public class lab3 {
	public static void main(String args[]) {
	   	if (args.length < 1) {
			System.err.println("Usage: lab3 <SourceFile>");
			System.exit(1);	
		}

		Yylex l = null;
		try {
		  for(int i=0;i<args.length;i++){
			File input=new File(args[i]);
		    String input_data=input.getName();
			int len=input_data.length();
		    l = new Yylex(new FileReader(args[i]));
			parser p = new parser(l);
	 
			CPP.Absyn.Program parse_tree = p.pProgram();
			new TypeChecker().typecheck(parse_tree);
	 		new Compiler().compile(parse_tree,input_data.substring(0, len-3));
		  }
		} catch (TypeException e) {
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

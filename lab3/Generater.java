import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;


public class Generater {

	public static void generate_class(File f){
		
		String separator=File.separator;
		String operation_system=System.getProperty("os.name");
	    String[] cmd=new String[3];
	    
		if(operation_system.startsWith("win")||operation_system.startsWith("Win")){
			 cmd[0]="cmd";
	    	  cmd[1]="/C";
	    
			 }
		else{
		      cmd[0]="/bin/sh";
	    	  cmd[1]="-c";
	    
		}
	  	
	   cmd[2]="java -jar jasmin.jar "+f.getName()
	                  +" -d good"+separator;     
	  
	    
        try {
			InputStream is=Runtime.getRuntime().exec(cmd).getErrorStream();
		    InputStreamReader reader=new InputStreamReader(is);
		    BufferedReader br = new BufferedReader(reader);  
            String error=br.readLine();
		    while(error!=null){
		    	 System.err.println("there is something wrong in command "+cmd[2]);
		    	 System.err.println(error);
		         error=br.readLine();
		    }
		    br.close();
		    reader.close();
		    is.close();
		} catch (IOException e) {
		 	e.printStackTrace();
		}
        finally{
        	 f.deleteOnExit();
        }
    	
     

		
	}
}

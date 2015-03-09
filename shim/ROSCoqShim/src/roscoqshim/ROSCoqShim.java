/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package roscoqshim;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import javax.swing.JOptionPane;

/**
 *
 * @author Abhishek
 */
public class ROSCoqShim {

  static class MsgInfo{
    long delay;
    double rad;
    double omega;

    @Override
    public String toString() {
      return ""+delay+","+rad+","+omega+"\n";
    }
    
  }
  
  static long parseZ(String exp)
  {
    String [] parts= exp.split(" ");
    String num=parts[parts.length-1];
    return Long.parseLong(num.split("%")[0]);
  }
  
  static double parseQ(PrintWriter input, BufferedReader result, String qexp) throws IOException
  {
      input.write("Eval vm_compute in QNumOp ("+qexp+"). \n");
      input.flush();
      long num= parseZ (result.readLine());
      result.readLine();      
      input.write("Eval vm_compute in QDenOp ("+qexp+"). \n");
      input.flush();
      long den= parseZ (result.readLine());
      result.readLine();      
      return ((double)num)/((double)den);
  }
  /**
   * @param args the command line arguments
   * @throws java.io.IOException
   * @throws java.lang.InterruptedException
   */
  public static void main(String[] args) throws IOException, InterruptedException {
    String command = "coqtop";
    List<String> commandParts = new LinkedList();
    commandParts.add(command);
    //commandParts.add("-ideslave");

    String initOptions = "-R . ROSCOQ -R ../../../ssrcorn/math-classes/src MathClasses -R ../../../ssrcorn CoRN";
    String[] initOpParts = initOptions.split(" ");

    commandParts.addAll(Arrays.asList(initOpParts));
    JOptionPane.showMessageDialog(null, commandParts);
    ProcessBuilder pb = new ProcessBuilder(commandParts);
    Process process = pb.directory(new File("C:\\Users\\Abhishek"
            + "\\Desktop\\PhDWork\\coq\\ROSCOQ")).start();

    PrintWriter input = new PrintWriter(new OutputStreamWriter(process.getOutputStream()), true);
    BufferedReader result = new BufferedReader(new InputStreamReader(process.getInputStream()));
    input.print("Require Export icreateConcrete.\n");
    input.flush();
    String respLine=result.readLine();

    Thread.sleep(30000);
    String humanResp
            = JOptionPane.showInputDialog("Enter target coordinates "
                    + "w.r.t robot's current position, e.g. -1,1");

    String[] coordinates = humanResp.split(",");
    //if(coordinates.length<2)
    String xc = coordinates[0];
    String yc = coordinates[1];
    
    String Cart2D = "{|X:= " +xc+ "; Y:= "+yc+"|}";
    
    input.write("Definition roboinp : Cart2D Q := "+ Cart2D +".\n"
            + "Definition robotOutput : list (Q ** Polar2D Q).\n" +
      "let t:= (eval vm_compute in (robotProgramInstance roboinp)) in\n" +
      "exact t.\n" +
      "Defined.\n");
    input.flush();
    
    Thread.sleep(1000);
    while(result.ready())
    {
      result.read(); // the stuff so far is not useful
    }
    
    input.write("Eval vm_compute in length robotOutput. \n");
    input.flush();
      
    
    respLine=result.readLine();
    result.readLine();
    final int numMesgs = Integer.parseInt(((respLine.split("="))[1]).trim());
    MsgInfo [] msg = new MsgInfo[numMesgs];
    for (int i=0;i<numMesgs;i++)
    {
       msg[i]=new MsgInfo();
       msg[i].delay=(long) (1000.0*parseQ(input, result, "nthDelay robotOutput "+i));
       msg[i].rad = parseQ(input, result, "nthLinVel robotOutput "+i);
       msg[i].omega = parseQ(input, result, "nthTheta robotOutput "+i);
       System.out.println(""+msg[i]);
    }
//    while (!respLine.isEmpty())
//    {
//      respLine=result.readLine();
//      resp=resp+respLine;
//    }
    
      
    // TODO code application logic here
  }

}

/*
 * Copyright (C) 2014 gunjan.
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 */

package com.github.rosjava.rosjava_catkin_package_a.my_pub_sub_tutorial;
//package com.github.rosjava_catkin_package_a.my_pub_sub_tutorial;

//import org.apache.commons.logging.Log;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.JOptionPane;
import org.ros.message.MessageListener;
import org.ros.namespace.GraphName;
import org.ros.node.AbstractNodeMain;
import org.ros.node.ConnectedNode;
import org.ros.node.NodeMain;
import org.ros.node.topic.Publisher;
import org.ros.node.topic.Subscriber;

/**
 * A simple {@link Subscriber} {@link NodeMain}.
 */
public class Listener extends AbstractNodeMain {

  @Override
  public GraphName getDefaultNodeName() {
    return GraphName.of("rosjava/listener");
  }

  static class MsgInfo{
    long delay;
    double rad;
    double omega;

    @Override
    public String toString() {
      return ""+delay+","+rad+","+omega+"\n";
    }

    synchronized void prepareVelMessage(geometry_msgs.Vector3 str)
    {
        str.setX(rad);
        str.setY(omega);
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
  @Override
  public void onStart(ConnectedNode connectedNode) {
      try {
          // final Log log = connectedNode.getLog();
          String command = "coqtop";
          List<String> commandParts = new LinkedList();
          commandParts.add(command);
          //commandParts.add("-ideslave");
          
          String initOptions = "-R . ROSCOQ -R ../../../ssrcorn/math-classes/src MathClasses -R ../../../ssrcorn CoRN";
          String[] initOpParts = initOptions.split(" ");
          
          commandParts.addAll(Arrays.asList(initOpParts));
          JOptionPane.showMessageDialog(null, commandParts);
          ProcessBuilder pb = new ProcessBuilder(commandParts);
          Process process = pb.directory(new File("/home/gunjan/"
                  + "padhaiWC/coq/ROSCOQ")).start();
          
          PrintWriter input = new PrintWriter(new OutputStreamWriter(process.getOutputStream()), true);
          BufferedReader result = new BufferedReader(new InputStreamReader(process.getInputStream()));
          input.print("Require Export icreateConcrete.\n");
          input.flush();
          String respLine;
          result.readLine();
          
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
          
        final Publisher<geometry_msgs.Vector3> publisher
                = connectedNode.newPublisher("icreate_vel", geometry_msgs.Vector3._TYPE);
          for (int i=0;i<numMesgs;i++)
          {
              Thread.sleep(msg[i].delay);
              geometry_msgs.Vector3 str = publisher.newMessage();
              msg[i].prepareVelMessage(str);
              publisher.publish(str);
              //Thread.sleep(100);
          }
      
      } catch (IOException ex) {
          Logger.getLogger(Listener.class.getName()).log(Level.SEVERE, null, ex);
      } catch (InterruptedException ex) {
          Logger.getLogger(Listener.class.getName()).log(Level.SEVERE, null, ex);
      }
  }
}

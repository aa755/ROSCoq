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
import geometry_msgs.Vector3;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;
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
public class Listener extends AbstractNodeMain 
        implements MessageListener<std_msgs.String>{

  @Override
  public GraphName getDefaultNodeName() {
    return GraphName.of("rosjava/listener");
  }

  Timer timer;
  int inpCtr=0;
    @Override
    public synchronized void onNewMessage(std_msgs.String t) {
      try {
          String humanResp=t.getData();
          String[] coordinates = humanResp.split(",");
          //if(coordinates.length<2)
          String xc = coordinates[0];
          String yc = coordinates[1];
          
          String Cart2D = "{|X:= " +xc+ "; Y:= "+yc+"|}";
          
          String inpCoqName = "inpMsg"+inpCtr;
          String outMsgsCoqName = "outMsgs"+inpCtr;
          input.write("Definition "+inpCoqName+" : Cart2D Q := "+ Cart2D +".\n"
                  + "Definition "+outMsgsCoqName+" : list (Q ** Polar2D Q).\n" +
                  "let t:= (eval vm_compute in (robotProgramInstance "
                  +inpCoqName+")) in\n" +
                  "exact t.\n" +
                  "Defined.\n");
          input.flush();
          
          Thread.sleep(1000);
          // remove the sleep and put appropriate number of readLines
          String out="";
          while(result.ready())
          {
              out=out+(char)result.read(); // the stuff so far is not useful
          }
          System.out.println("result of the definitions:"+ out);
          input.write("Eval vm_compute in length "+outMsgsCoqName+". \n");
          input.flush();
          
          String respLine;
          
          respLine=result.readLine();
          result.readLine();
          final int numMesgs = Integer.parseInt(((respLine.split("="))[1]).trim());
          MotorMsg msg;// = new MotorMsg[numMesgs];
          long totdelay=0;
          for (int i=0;i<numMesgs;i++)
          {
              msg=new MotorMsg(spub);
              msg.delay=(long) (1000.0*parseQ(input, result, "nthDelay "+outMsgsCoqName+" "+i));
              msg.rad = parseQ(input, result, "nthLinVel "+outMsgsCoqName+" "+i);
              msg.omega = parseQ(input, result, "nthTheta "+outMsgsCoqName+" "+i);
              System.out.println(""+msg);
              totdelay=totdelay+msg.delay;
              timer.schedule(msg, totdelay);
          } 
          
      } catch (IOException | InterruptedException ex) {
          Logger.getLogger(Listener.class.getName()).log(Level.SEVERE, null, ex);
      }

    }


  static class MotorMsg extends TimerTask{
    long delay; // not used
    double rad;
    double omega;
    ROSPublisher rpub;

    @Override
    public String toString() {
      return ""+delay+","+rad+","+omega+"\n";
    }

    MotorMsg(ROSPublisher rpub)
    {
        this.rpub=rpub;
    }
    
    void prepareVelMessage(geometry_msgs.Vector3 str)
    {
        str.setX(rad);
        str.setY(omega);
    }

    @Override
    public void run() {
        rpub.publishMotorMsg(this);
    }
    
  }

  /**
   * Wraps around the ROSJava Publisher class
   * to ensure synchronized sending of messages.
   * At the time of making this class, the ROSJava
   * documentation was not clear whether Publisher
   * is inherently threadsafe.
   * TODO: make the message type and topic name generic
   */
    static class ROSPublisher {

        Publisher<geometry_msgs.Vector3> publisher;

        public ROSPublisher(ConnectedNode connectedNode) {
            publisher
                    = connectedNode.newPublisher("icreate_vel", geometry_msgs.Vector3._TYPE);
            publisher.setLatchMode(true);
        }

        synchronized void publishMotorMsg(MotorMsg msg) {
            geometry_msgs.Vector3 str = publisher.newMessage();
            msg.prepareVelMessage(str);
            publisher.publish(str);
        }
    }

  static long parseZ(String exp)
  {
    String [] parts= exp.split(" ");
    String num=parts[parts.length-1];
    String numNoScope=num.split("%")[0];
    if(numNoScope.startsWith("("))
    {
        numNoScope=numNoScope.substring(1, numNoScope.length()-1);
    }
    return Long.parseLong(numNoScope);
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
  
    PrintWriter input;
    BufferedReader result;
  
  ROSPublisher spub;
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
          
          input = new PrintWriter(new OutputStreamWriter(process.getOutputStream()), true);
          result = new BufferedReader(new InputStreamReader(process.getInputStream()));
          input.print("Require Export icreateConcrete.\n");
          input.flush();
          result.readLine();
          spub=new ROSPublisher(connectedNode);
         Thread.sleep(30000);
         // String humanResp
           //       = JOptionPane.showInputDialog("Enter target coordinates "
             //             + "w.r.t robot's current position, e.g. -1,1");
          
         timer=new Timer();
          
      
      } catch (IOException | InterruptedException ex) {
          Logger.getLogger(Listener.class.getName()).log(Level.SEVERE, null, ex);
      }
      
          Subscriber<std_msgs.String> subscriber 
            = connectedNode.newSubscriber("ROSCoq/TARGETPOS", std_msgs.String._TYPE);
        
    // This CancellableLoop will be canceled automatically when the node shuts
        // down.
        subscriber.addMessageListener(this);

  }
}

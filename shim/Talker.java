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

import org.ros.concurrent.CancellableLoop;
import org.ros.namespace.GraphName;
import org.ros.node.AbstractNodeMain;
import org.ros.node.ConnectedNode;
import org.ros.node.NodeMain;
import org.ros.node.topic.Publisher;
/**
 * A simple {@link Publisher} {@link NodeMain}.
 */
public class Talker extends AbstractNodeMain {

  @Override
  public GraphName getDefaultNodeName() {
    return GraphName.of("rosjava/talker");
  }

  class RoboCancellableLoop extends CancellableLoop{
        final Publisher<geometry_msgs.Twist> publisher;
      @Override
      protected void setup() {
      }

        public RoboCancellableLoop(Publisher<geometry_msgs.Twist> publisher) {
            this.publisher = publisher;
        }

      
      @Override
      protected void loop() throws InterruptedException {
        geometry_msgs.Twist str = publisher.newMessage();
        str.getAngular().setZ(0.1);
        publisher.publish(str);
        Thread.sleep(100);
      }

      
  }
          

  @Override
  public void onStart(final ConnectedNode connectedNode) {
     final Publisher<geometry_msgs.Twist> publisher
     = connectedNode.newPublisher("mobile_base/commands/velocity", geometry_msgs.Twist._TYPE);
      
    // This CancellableLoop will be canceled automatically when the node shuts
    // down.
    connectedNode.executeCancellableLoop(new RoboCancellableLoop(publisher));
    
  }
}

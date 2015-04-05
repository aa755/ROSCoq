/*
 * Copyright (C) 2014 Cornell University.
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
package com.github.rosjava.roscoqshim.my_pub_sub_tutorial;
//package com.github.rosjava_catkin_package_a.my_pub_sub_tutorial;

import javax.swing.JOptionPane;
import org.ros.namespace.GraphName;
import org.ros.node.AbstractNodeMain;
import org.ros.node.ConnectedNode;
import org.ros.node.NodeMain;
import org.ros.node.topic.Publisher;

/**
 * A simple {@link Publisher} {@link NodeMain}.
 */
public class ExternalAgent extends AbstractNodeMain {

    @Override
    public GraphName getDefaultNodeName() {
        return GraphName.of("rosjava/ROSCoq/ExternalAgent");
    }

    @Override
    public void onStart(final ConnectedNode connectedNode) {
        final Publisher<std_msgs.String> publisher
                = connectedNode.newPublisher("ROSCoq/TARGETPOS", std_msgs.String._TYPE);
    publisher.setLatchMode(true);

    String humanResp = JOptionPane.showInputDialog("Enter target coordinates"
                + "w.r.t robot's current position, e.g. -1,1");
    
    std_msgs.String str = publisher.newMessage();
    str.setData(humanResp);
    publisher.publish(str);
    }
}

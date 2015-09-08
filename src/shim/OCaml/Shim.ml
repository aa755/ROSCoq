
let rpc = new XmlRpc.client "http://localhost:11311"

(*
let printSysState =
let result = rpc#call "getSystemState" [`String "hello!"] in
print_endline (XmlRpc.dump result);; *)

(* must be a fully qualified ROS topic name and ROS message type *)
type topicInfo = {name : string ; rtype: string};;
type nodeInfo = {publish : topicInfo list ;subscribe : topicInfo list};;

let nodeName : string = "/ROSCoqShim";; (* make it a module parameter *)
let hostName : string = "locahost";; (* make it a module parameter *)

let getURI (port : string) = "http://localhost:" ^ port;;

let registerAsPublisher (tp: topicInfo) (port: string) =
	let result = rpc#call "registerPublisher" [`String nodeName ;
				`String (tp.name); `String (tp.rtype); `String (getURI port)] in
	print_endline (XmlRpc.dump result);;

let chatterTopic : topicInfo = {name = "chatter" ; rtype="std_msgs/String"};;
 	 
let main () =
	registerAsPublisher chatterTopic "1919";;
	

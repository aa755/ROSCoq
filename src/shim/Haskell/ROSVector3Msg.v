Require Import RoshaskMsg.
Require Import String.
Require Import ExtrHaskellString.



Extraction Language Haskell.

Require Import RoshaskTypes.

(** temporary example for generation of Coq types for ROS messages, 
   and extraction to corresponding Haskell messages. 
  This file will be deleted once the machinery for automatic generation of files like this is in place.*)

Record ROS_Geometry_Vector3 := mkVector3
                                 {_x:RoshaskFloat; _y:RoshaskFloat; _z:RoshaskFloat
                                 }.

Extract Inductive ROS_Geometry_Vector3 => "Ros.Geometry_msgs.Vector3.Vector3"
                                            [ "Ros.Geometry_msgs.Vector3.Vector3"].

Extract Constant _x => "Ros.Geometry_msgs.Vector3._x".
Extract Constant _y => "Ros.Geometry_msgs.Vector3._y".
Extract Constant _z => "Ros.Geometry_msgs.Vector3._z".

Require Import RoshaskNodeMonad.

Require Import RoshaskTopic.

Axiom subscribe_ROS_Geometry_Vector3 : TopicName -> Node (RTopic ROS_Geometry_Vector3).
Extract Constant  subscribe_ROS_Geometry_Vector3 => "(Ros.ROSCoqUtil.subscribeCoList)".

Axiom publish_ROS_Geometry_Vector3 : TopicName -> RTopic ROS_Geometry_Vector3 -> Node unit.
Extract Constant  publish_ROS_Geometry_Vector3 => "(Ros.ROSCoqUtil.publishCoList)".

(*
Axiom advertise_Vector3  : TopicName -> Node (Chan ROS_Geometry_Vector3).
Extract Constant advertise_Vector3 => "Ros.ROSCoqUtil.advertiseNewChan".
*)
Instance ROSMsgInstance_ROS_Geometry_Vector3 : ROSMsgType ROS_Geometry_Vector3 :=
  Build_ROSMsgType _  subscribe_ROS_Geometry_Vector3  publish_ROS_Geometry_Vector3.
(*advertise_Vector3.*)



(* Corresponding Haskell file (autogenerated by roshask:


{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
module Ros.Geometry_msgs.Vector3 where
import qualified Prelude as P
import qualified Data.Typeable as T
import Control.Applicative
import Ros.Internal.RosBinary
import Ros.Internal.Msg.MsgInfo
import qualified GHC.Generics as G
import qualified Data.Default.Generics as D
import Foreign.Storable (Storable(..))
import qualified Ros.Internal.Util.StorableMonad as SM
import Lens.Family.TH (makeLenses)
import Lens.Family (view, set)

data Vector3 = Vector3 { _x :: P.Double
                       , _y :: P.Double
                       , _z :: P.Double
                       } deriving (P.Show, P.Eq, P.Ord, T.Typeable, G.Generic)

$(makeLenses ''Vector3)

instance RosBinary Vector3 where
  put obj' = put (_x obj') *> put (_y obj') *> put (_z obj')
  get = Vector3 <$> get <*> get <*> get

instance Storable Vector3 where
  sizeOf _ = sizeOf (P.undefined::P.Double) +
             sizeOf (P.undefined::P.Double) +
             sizeOf (P.undefined::P.Double)
  alignment _ = 8
  peek = SM.runStorable (Vector3 <$> SM.peek <*> SM.peek <*> SM.peek)
  poke ptr' obj' = SM.runStorable store' ptr'
    where store' = SM.poke (_x obj') *> SM.poke (_y obj') *> SM.poke (_z obj')

instance MsgInfo Vector3 where
  sourceMD5 _ = "4a842b65f413084dc2b10fb484ea7f17"
  msgTypeName _ = "geometry_msgs/Vector3"

instance D.Default Vector3

*)



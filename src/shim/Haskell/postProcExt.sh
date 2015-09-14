shopt -s extglob

# what if this line was in a string? 
ORIG="import qualified Prelude"
REP="import qualified Prelude
import qualified Ros.Node
import qualified Ros.Topic (repeatM)
import qualified Ros.ROSCoqUtil
import qualified Control.Concurrent
import qualified Ros.Std_msgs.String
import qualified Ros.Geometry_msgs.Vector3
import qualified Data.Bits
import qualified Data.Ratio
import qualified Data.Char"

REP="${REP//+(
)/\\n}"

sed -i "s/$ORIG/$REP/g" $1


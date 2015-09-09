shopt -s extglob

# what if this line was in a string? 
ORIG="import qualified Prelude"
REP="import qualified Prelude
import qualified Ros.Node
import qualified Ros.Topic (repeatM)
import qualified Ros.ROSCoqUtil
import qualified Ros.Std_msgs.String
import qualified Data.Bits
import qualified Data.Char"

REP="${REP//+(
)/\\n}"

sed -i "s/$ORIG/$REP/g" $1


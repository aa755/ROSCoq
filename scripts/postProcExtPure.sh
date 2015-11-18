shopt -s extglob

# what if this line was in a string? 
ORIG="import qualified Prelude"
REP="import qualified Prelude
import qualified Data.Bits
import qualified Data.Ratio
import qualified Data.Char"

REP="${REP//+(
)/\\n}"

sed -i "s/$ORIG/$REP/g" $1

echo "main :: GHC.Base.IO ()
main = Prelude.putStrLn toPrint" >> $1

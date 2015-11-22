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



# what if this line was in a string? 
ORIG="ztoString = PleaseFixMe"
REP="ztoString x =
        let (q,r) = Prelude.quotRem x 100 in
        let rs = (Prelude.show (Prelude.abs r)) in
        let rss = (if ((Prelude.<) (Prelude.abs r) 10) then Prelude.concat [\"0\",rs] else rs) in
        let out = Prelude.concat [(Prelude.show q), \".\",rss] in
        (if ((Prelude.\&\&) ((Prelude.==) q 0) ((Prelude.<) r 0)) then Prelude.concat [\"-\", out] else out)"

REP="${REP//+(
)/\\n}"

sed -i "s/$ORIG/$REP/g" $1

echo "main :: GHC.Base.IO ()
main = Prelude.putStrLn toPrint" >> $1

# Old versions of Coq are missing many files containing Extraction directives, especially for Haskell
# This script can fetch them for you

wget https://raw.githubusercontent.com/coq/coq/trunk/plugins/extraction/ExtrHaskellBasic.v -O ExtrHaskellBasic.v
wget https://raw.githubusercontent.com/coq/coq/trunk/plugins/extraction/ExtrHaskellZInteger.v -O extraction/ExtrHaskellZInteger.v
wget https://raw.githubusercontent.com/coq/coq/trunk/plugins/extraction/ExtrHaskellZNum.v -O extraction/ExtrHaskellZNum.v



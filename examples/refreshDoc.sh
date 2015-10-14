set -e

scons --site-dir ../site_scons/ icreateMoveToLocExt.vo


rm -rf coqdoc
cp SConstruct SConstruct.backup
cat SConstruct.coqdoc >> SConstruct
scons --site-dir ../site_scons/ coqdoc
cp SConstruct.backup SConstruct

cp icreateMoveToLoc.svg coqdoc/
cd coqdoc; ../../scripts/patchNoCache.sh

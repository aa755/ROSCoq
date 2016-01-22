import os, glob, string

dirs_to_compile = ['src']

nodes = map(lambda x: './' + x, dirs_to_compile)
dirs = []
vs = []


env = DefaultEnvironment(ENV = os.environ, tools=['default','Coq','CoqQuick'])

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if (node.endswith('.v')
   and not node.endswith('CRMisc/ContField.v')
   and not node.endswith('CRMisc/PointWiseRing.v')
   and not node.endswith('CRMisc/OldMetricAsNew.v')
   and not node.endswith('CartAR.v')
   and not node.endswith('ProbTh.v')
   and not node.endswith('shim/oldJavaShim/icreateConcrete.v')
   and not node.endswith('Everything.v')
   and not node.endswith('trash.v')):
    vs += [File(node)]
  if os.path.isdir(node):
    dirs += [node]
    nodes += glob.glob(node + '/*')

includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:]))


#Note that ROSCoq depends on Corn (which depends on MathClasses). Please edit the line below, depending on how you installed them. 
# See https://github.com/c-corn/corn
Rs = '-R src ROSCOQ -R dependencies/corn CoRN -R dependencies/corn/math-classes/src MathClasses'
coqcmd = 'coqc ${str(SOURCE)[:-2]} ' + Rs
coqcmdquick = 'coqc ${str(SOURCE)[:-2]} -quick ' + Rs

env['COQFLAGS'] = Rs

quick = ARGUMENTS.get('quick', 0)
if int(quick):
  for node in vs: env.CoqQuick(node, COQCMDQUICK=coqcmdquick)
else:
  for node in vs: env.Coq(node, COQCMD=coqcmd)


os.system('coqdep ' + ' '.join(map(str, vs)) + ' ' + includes + ' ' + Rs + ' > deps')
ParseDepends('deps')


#open('coqidescript', 'w').write('#!/bin/sh\ncoqide ' + Rs + ' $@ \n')
#os.chmod('coqidescript', 0755)



# Only after a normal build (for .vos) is complete, one can enable the 2 lines below to enable coqdoc generation (using scons coqdoc).  dont forget to then patch the generated HTML to disable caching. run patchNoCache.sh in the generated coqdoc/ directory. also see updateDoc.sh
# enabling it before somehow messes the dependency analysis done by scons
#mc_vs, mc_vos, mc_globs = env.SConscript(dirs='dependencies/corn/') # CoRN + MathClasses
#env.CoqDoc(env.Dir('coqdoc'), vs+mc_vs, COQDOCFLAGS='-utf8 --toc --interpolate --no-lib-name --coqlib http://coq.inria.fr/library')

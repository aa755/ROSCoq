import os, glob, string

# Removing examples directory since we do not need it every time.
dirs_to_compile = ['.']

nodes = map(lambda x: './' + x, dirs_to_compile)
dirs = []
vs = []

env = DefaultEnvironment(ENV = os.environ, tools=['default','Coq'])

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if (node.endswith('.v')
   and not node.endswith('CRMisc/ContField.v')
   and not node.endswith('CRMisc/PointWiseRing.v')
   and not node.endswith('Everything.v')
   and not node.endswith('trash.v')
   and not node.endswith('train.v')
   and not node.endswith('CartAR.v')):
    vs += [File(node)]
  if os.path.isdir(node):
    dirs += [node]
    nodes += glob.glob(node + '/*')

includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:]))
Rs = '-R . ROSCOQ -R ../../../ssrcorn/math-classes/src MathClasses -R ../../../ssrcorn CoRN'
coqcmd = 'coqc ${str(SOURCE)[:-2]} ' + Rs

env['COQFLAGS'] = Rs

for node in vs: env.Coq(node, COQCMD=coqcmd)


os.system('coqdep ' + ' '.join(map(str, vs)) + ' ' + includes + ' ' + Rs + ' > deps')
ParseDepends('deps')

mc_vs, mc_vos, mc_globs = env.SConscript(dirs='../../../ssrcorn/math-classes/src')
#corn_vs, corn_vos, corn_globs = env.SConscript(dirs='../../../ssrcorn')

#open('coqidescript', 'w').write('#!/bin/sh\ncoqide ' + Rs + ' $@ \n')
#os.chmod('coqidescript', 0755)

env.CoqDoc(env.Dir('coqdoc'), vs+mc_vs, COQDOCFLAGS='-utf8 --toc -g --no-lib-name --coqlib http://coq.inria.fr/library')

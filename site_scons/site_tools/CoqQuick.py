# -*- coding: utf-8 -*-

import SCons.Defaults, SCons.Tool, SCons.Util, os

CoqQuick = SCons.Builder.Builder(
  action = '$COQCMDQUICK',
  suffix = '.vio',
  src_suffix = '.v')


def generate(env):
  env['COQC'] = 'coqc'
  env['COQCMD'] = '$COQC $COQFLAGS -q -quick $SOURCE'
  env.Append(BUILDERS = {'CoqQuick': CoqQuick})

def exists(env):
  return env.Detect('coqc')

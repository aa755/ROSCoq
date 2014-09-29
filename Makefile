


Process.vo : Process.v
	coqc $<

roscore.vo : roscore.v Process.vo
	coqc $<
	


ADC.vo : ADC.v core.vo
	coqc $<

core.vo : core.v
	coqc $<

%.tex: %.v
	coqc $<
	coqdoc   -l --latex --interpolate --body-only $< -o $(@)	

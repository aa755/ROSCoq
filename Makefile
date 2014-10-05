ROSCyberPhysicalSystem.vo : ROSCyberPhysicalSystem.v roscore.vo
	coqc $<
	

roscore.vo : roscore.v Process.vo
	coqc $<

Process.vo : Process.v core.vo
	coqc $<


ADC.vo : ADC.v core.vo
	coqc $<

core.vo : core.v
	coqc $<

%.tex: %.v
	coqc $<
	coqdoc   -l --latex --interpolate --body-only $< -o $(@)	

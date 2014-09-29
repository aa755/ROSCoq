Require Export Process.


Record BaseMotorState :=
{
  vFw : R;
  turning : R
}.


Definition BaseOutDev : MemoryLessOutDev BaseMotorState BaseMotorState.



Record iState := {
  posX : R;
  posY : R;
  orient : R; (* ideally 0 to 2 pi *)
  bms : BaseMotorState
}.



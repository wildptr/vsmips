function bool eqnz(RegIndex a, RegIndex b) =
  a == b && a != 5'b0;

function bool data_hazard(RegIndex wa_E, RegIndex wa_M,
                          RegIndex ra1_D, RegIndex ra2_D) =
  eqnz(ra1_D, wa_E) || eqnz(ra2_D, wa_E) ||
  eqnz(ra1_D, wa_M) || eqnz(ra2_D, wa_M);

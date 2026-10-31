/*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 */

`ifndef GURU_LIBRARY_SV
`define GURU_LIBRARY_SV

virtual class verilog_bits #(parameter n, parameter last, parameter first);
  static function logic[last-first:0] extract(logic [n-1:0] val);
    extract = val[last:first];
  endfunction
  static function logic[n-1:0] update(logic [n-1:0] s, logic [last-first:0] upd_val);
    s[last:first] = upd_val;
    update = s;
  endfunction
endclass

virtual class verilog_var_array #(parameter n, parameter sizeK, parameter m);
  static function logic [sizeK-1:0] extract(logic [n-1:0][sizeK-1:0] s, logic [m-1:0] idx);
    extract = s[idx];
  endfunction
  static function logic [n-1:0][sizeK-1:0] update(logic [n-1:0][sizeK-1:0] s, logic [m-1:0] idx, logic [sizeK-1:0] val);
    s[idx] = val;
    update = s;
  endfunction
endclass

virtual class verilog_const_array #(parameter n, parameter sizeK, parameter idx);
  static function logic [sizeK-1:0] extract(logic [n-1:0][sizeK-1:0] s);
    extract = s[idx];
  endfunction
  static function logic [n-1:0][sizeK-1:0] update(logic [n-1:0][sizeK-1:0] s, logic [sizeK-1:0] val);
    s[idx] = val;
    update = s;
  endfunction
endclass

module verilog_sram#(parameter n=1, parameter clgn=1, parameter sizeK=1, parameter p=1,
                     parameter init=0, parameter def=0,
                     parameter logic [n*sizeK-1:0] initVal = '0)(
  input logic [p-1:0][clgn-1:0] Rq,
  input logic [p-1:0] RqEn,
  input logic [clgn-1:0] WrIdx,
  input logic [sizeK-1:0] WrVal,
  input logic WrEn,
  output logic [p-1:0][sizeK-1:0] Rp,
  input clk
);
  logic [sizeK-1:0] mem[n-1:0];
  int i, j;
`ifndef SYNTHESIS
  // synopsys translate_off
  initial begin
    if (init) begin
      if (def) begin
        for(i = 0; i < n; i=i+1) begin
          mem[i] = '0;
        end
      end else begin
        for(i = 0; i < n; i=i+1) begin
          mem[i] = initVal[i*sizeK +: sizeK];
        end
      end
    end
  end
  // synopsys translate_on
`endif
  always @(posedge clk) begin
    for (j = 0; j < p; j=j+1) begin
      if (RqEn[j]) begin
        Rp[j] <= mem[Rq[j]];
      end
    end
    if (WrEn) begin
      mem[WrIdx] <= WrVal;
    end
  end
endmodule

module verilog_mem#(parameter n=1, parameter clgn=1, parameter sizeK=1, parameter p=1,
                    parameter init=0, parameter def=0,
                    parameter logic [n*sizeK-1:0] initVal = '0)(
  input logic [p-1:0][clgn-1:0] Rq,
  input logic [p-1:0] RqEn,
  input logic [clgn-1:0] WrIdx,
  input logic [sizeK-1:0] WrVal,
  input logic WrEn,
  output logic [p-1:0][sizeK-1:0] Rp,
  input clk,
  input rst_n
);
  logic [p-1:0] sramRqEn;
  logic [p-1:0] inBounds;
  logic [p-1:0][sizeK-1:0] sramRp;
  int i, j;

  always_comb begin
    for (i = 0; i < p; i=i+1) begin
      sramRqEn[i] = RqEn[i] && (Rq[i] <= clgn'(n - 1));
      Rp[i]       = inBounds[i] ? sramRp[i] : '0;
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      inBounds <= '0;
    end else begin
      for (j = 0; j < p; j=j+1) begin
        if (RqEn[j]) begin
          inBounds[j] <= (Rq[j] <= clgn'(n - 1));
        end
      end
    end
  end

  verilog_sram#(
    .n(n),
    .clgn(clgn),
    .sizeK(sizeK),
    .p(p),
    .init(init),
    .def(def),
    .initVal(initVal)
  ) u_sram (
    .Rq(Rq),
    .RqEn(sramRqEn),
    .WrIdx(WrIdx),
    .WrVal(WrVal),
    .WrEn(WrEn && (WrIdx <= clgn'(n - 1))),
    .Rp(sramRp),
    .clk(clk)
  );
endmodule

`endif

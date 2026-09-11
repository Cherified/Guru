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
  logic [sizeK-1:0] mem[n-1:0];
  logic [p-1:0][sizeK-1:0] RpWire;
  int i;
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
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      Rp <= '0;
    end else begin
      RpWire = Rp;
      for (i = 0; i < p; i=i+1) begin
        if (RqEn[i]) begin
          RpWire[i] = (Rq[i] < n) ? mem[Rq[i]] : '0;
        end
      end
      Rp <= RpWire;
      if (WrEn && WrIdx < n) begin
        mem[WrIdx] <= WrVal;
      end
    end
  end
endmodule

(* DONT_TOUCH = "TRUE" *)
module sync_ff2 (
  input  logic clk,
  input  logic rst_n,
  input  logic d,
  output logic q
);
  (* ASYNC_REG = "TRUE" *) logic sync1;
  (* ASYNC_REG = "TRUE" *) logic sync2;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      sync1 <= 1'b0;
      sync2 <= 1'b0;
    end else begin
      sync1 <= d;
      sync2 <= sync1;
    end
  end

  assign q = sync2;
endmodule

(* DONT_TOUCH = "TRUE" *)
module sync_opt #(parameter WIDTH = 2) (
  input  logic             clk,
  input  logic             rst_n,
  input  logic [WIDTH-1:0] d,
  output logic [WIDTH-1:0] q
);
  logic sync_valid;
  sync_ff2 u_sync_valid (
    .clk  (clk),
    .rst_n(rst_n),
    .d    (d[0]),
    .q    (sync_valid)
  );
  assign q = {d[WIDTH-1:1], sync_valid};
endmodule

// Recommended SDC / Tcl constraints for CDC synchronizers:
//
// # 1. Define the clock domains (example periods: 10ns core, 40ns peripheral)
// create_clock -name clk_core       -period 10.0 [get_ports clk_core]
// create_clock -name clk_peripheral -period 40.0 [get_ports clk_peripheral]
//
// # 2. Prevent synthesis/PnR from optimizing, retiming, or flattening the synchronizers
// set_dont_touch [get_designs sync_ff2]
// set_dont_touch [get_designs sync_opt]
//
// # 3. False-path the asynchronous input to the first flip-flop (sync1) of every 2-FF synchronizer
// set_false_path -to [get_pins -hierarchical *sync_ff2_cdc_inst_*/sync1/D]
// set_false_path -to [get_pins -hierarchical *sync_opt_cdc_inst_*/u_sync_valid/sync1/D]
//
// # 4. Disable hold checks between asynchronous clock domains
// set_false_path -hold -from [get_clocks clk_core]       -to [get_clocks clk_peripheral]
// set_false_path -hold -from [get_clocks clk_peripheral] -to [get_clocks clk_core]
//
// # 5. Bound the wire/datapath skew of Option k payload bits (d[WIDTH-1:1])
// #    so they are guaranteed to arrive within 1 destination clock cycle (before sync_valid rises):
// set_max_delay 10.0 -datapath_only \
//   -from [get_clocks clk_peripheral] \
//   -to   [get_clocks clk_core] \
//   -through [get_pins -hierarchical *sync_opt_cdc_inst_*/d*]
//
// set_max_delay 40.0 -datapath_only \
//   -from [get_clocks clk_core] \
//   -to   [get_clocks clk_peripheral] \
//   -through [get_pins -hierarchical *sync_opt_cdc_inst_*/d*]
`endif

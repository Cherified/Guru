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
`endif

`ifndef GURU_LIBRARY_SV
`define GURU_LIBRARY_SV

virtual class verilog_bits #(parameter n, parameter last, parameter first);
  static function logic[last-first:0] extract(logic [n-1:0] val);
    extract = val[last:first];
  endfunction
endclass

virtual class verilog_var_array #(parameter n, parameter sizeK, parameter m);
  static function logic [sizeK-1:0] extract(logic [n-1:0][sizeK-1:0] s, logic [m-1:0] idx);
    extract = s[idx];
  endfunction
endclass

virtual class verilog_const_array #(parameter n, parameter sizeK, parameter idx);
  static function logic [sizeK-1:0] extract(logic [n-1:0][sizeK-1:0] s);
    extract = s[idx];
  endfunction
endclass

module verilog_mem#(parameter n=1, parameter clgn=1, parameter sizeK=1, parameter p=1,
                    parameter init=0, parameter def=0, parameter ascii=0, parameter string argName="",
                    parameter offset=0, parameter size=0)(
  input logic [p-1:0][clgn-1:0] Rq,
  input logic [p-1:0] RqEn,
  input logic [clgn-1:0] WrIdx,
  input logic [sizeK-1:0] WrVal,
  input logic WrEn,
  output logic [p-1:0][sizeK-1:0] Rp,
  input CLK,
  input RESET
);
  logic [sizeK-1:0] mem[n-1:0];
  logic [p-1:0][sizeK-1:0] RpWire;
  string file;
  int i;
  // synthesis translate_off
  initial begin
    if (init) begin
      if (def) begin
        for(i = 0; i < n; i=i+1) begin
          mem[i] = 0;
        end
      end else begin
        $value$plusargs({argName, "=%s"}, file);
        if (ascii) begin
          $readmemh(file, mem, offset, size);
        end else begin
          $readmemb(file, mem, offset, size);
        end
      end
    end
  end
  // synthesis translate_on
  always @(posedge CLK) begin
    RpWire = Rp;
    for (i = 0; i < p; i=i+1) begin
      if (RqEn[i]) begin
        RpWire[i] = mem[Rq[i]];
      end
    end
    Rp <= RpWire;
    if (WrEn) begin
      mem[WrIdx] <= WrVal;
    end
  end
endmodule
`endif

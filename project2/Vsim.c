/***********************************************************
 * Project 2
 * CDA4102 Fall 2025
 * Date: Mon Nov 03, 2025
 * Due: Wed Nov 12, 2025 at 11:30pm
 * File: Vsim.c
 **********************************************************/

/* On my honor, I have neither given nor received
 * unauthorized aid on this assignment. */

#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define OP_beq  0
#define OP_bne  4
#define OP_blt  8
#define OP_sw   12
#define OP_add  1
#define OP_sub  5
#define OP_and  9
#define OP_or   13
#define OP_addi 2
#define OP_andi 6
#define OP_ori  10
#define OP_sll  14
#define OP_sra  18
#define OP_lw   22
#define OP_jal  3
#define OP_break 127

#define opcode(ins) ((ins) & 127)
#define rd(ins) ((ins) >> 7 & 31)
#define rs1(ins) ((ins) >> 15 & 31)
#define rs2(ins) ((ins) >> 20 & 31)
#define imm1(ins) (((ins) >> 7 & 31) | ((ins) >> 20 & ~31))
#define imm3(ins) ((ins) >> 20)
#define imm4(ins) ((ins) >> 12)
#define mem32(addr) mem[((addr) - 256) >> 2]

static int32_t
  *mem, mem_data, mem_end,
  pc = 256,
  pre_issue[4],
  pre_alu1_ins, pre_alu1_addr, pre_alu1_val,
  pre_alu1_ins2, pre_alu1_addr2, pre_alu1_val2,
  pre_alu2_ins, pre_alu2_lhs, pre_alu2_rhs,
  pre_alu2_ins2, pre_alu2_lhs2, pre_alu2_rhs2,
  pre_alu3_ins, pre_alu3_lhs, pre_alu3_rhs,
  pre_alu3_ins2, pre_alu3_lhs2, pre_alu3_rhs2,
  post_alu2_ins, post_alu2_val,
  post_alu3_ins, post_alu3_val,
  pre_mem_ins, pre_mem_addr, pre_mem_val,
  post_mem_ins, post_mem_val,
  regs[32],
  willwrite;

__attribute__((format(printf, 1, 2)))
static void err(const char *format, ...)
{
  va_list ap;
  char buf[2048];
  char *s = buf + 7;
  memcpy(buf, "error: ", 7);
  va_start(ap, format);
  vsnprintf(s, sizeof(buf) - 7, format, ap);
  va_end(ap);
  for (; *s; ++s)
    if (*s < 0x20 || *s == 0x7f)
      *s = '?';
  *(s++) = '\n';
  write(2, buf, s - buf);
}

#define err_sys_(format, ...) err(format ": %s", __VA_ARGS__)
#define err_sys(...) err_sys_(__VA_ARGS__, strerror(errno))

static void program_load(const char *filename)
{
  int fd = open(filename, O_RDONLY);
  if (fd < 0) {
    err_sys("could not open '%s'", filename);
    exit(1);
  }

  struct stat st;
  if (fstat(fd, &st)) {
    err_sys("could not stat '%s'", filename);
    exit(1);
  }

  ssize_t read_size;
  char buf[1024];
  unsigned long mem_size = st.st_size >> 5;
  mem = calloc(mem_size, sizeof(int32_t));
  int32_t *cur = mem;
  int32_t *end = mem + mem_size;
  int nbits = 32;
  int32_t value = 0;

  while ((read_size = read(fd, buf, sizeof(buf))) > 0) {
    for (ssize_t i = 0; i < read_size; ++i) {
      if (buf[i] == '0') {
        value = value << 1;
      } else if (buf[i] == '1') {
        value = value << 1 | 1;
      } else {
        continue;
      }
      if (--nbits) {
        continue;
      }
      *(cur++) = value;
      if (value == 127) {
        mem_data = (char *)cur - (char *)mem + 256;
      }
      if (cur == end) {
        goto done;
      }
      nbits = 32;
      value = 0;
    }
  }

  if (read_size) {
    err_sys("read");
    exit(1);
  }

done:
  close(fd);
  mem_end = (char *)cur - (char *)mem + 256;
}

static int32_t rget(int id)
{
  return regs[id];
}

static void rset(int id, int32_t val)
{
  if (id) {
    regs[id] = val;
    willwrite &= ~(1 << id);
  }
}

static void print_instruction(FILE *out, int32_t ins)
{
  if (!ins) {
    fputc('\n', out);
    return;
  }
  fputs(" [", out);
#define CASE(op, ...) case OP_ ## op: fprintf(out, #op " " __VA_ARGS__); break
  switch (opcode(ins)) {
    CASE(beq,   "x%d, x%d, #%d", rs1(ins), rs2(ins), imm1(ins));
    CASE(bne,   "x%d, x%d, #%d", rs1(ins), rs2(ins), imm1(ins));
    CASE(blt,   "x%d, x%d, #%d", rs1(ins), rs2(ins), imm1(ins));
    CASE(sw,    "x%d, %d(x%d)",  rs1(ins), imm1(ins), rs2(ins));
    CASE(add,   "x%d, x%d, x%d", rd(ins), rs1(ins), rs2(ins));
    CASE(sub,   "x%d, x%d, x%d", rd(ins), rs1(ins), rs2(ins));
    CASE(and,   "x%d, x%d, x%d", rd(ins), rs1(ins), rs2(ins));
    CASE(or,    "x%d, x%d, x%d", rd(ins), rs1(ins), rs2(ins));
    CASE(addi,  "x%d, x%d, #%d", rd(ins), rs1(ins), imm3(ins));
    CASE(andi,  "x%d, x%d, #%d", rd(ins), rs1(ins), imm3(ins));
    CASE(ori,   "x%d, x%d, #%d", rd(ins), rs1(ins), imm3(ins));
    CASE(sll,   "x%d, x%d, #%d", rd(ins), rs1(ins), imm3(ins));
    CASE(sra,   "x%d, x%d, #%d", rd(ins), rs1(ins), imm3(ins));
    CASE(lw,    "x%d, %d(x%d)",  rd(ins), imm3(ins), rs1(ins));
    CASE(jal,   "x%d, #%d",      rd(ins), imm4(ins));
    case OP_break: fputs("break", out);
  }
#undef CASE
  fputs("]\n", out);
}

static void program_simulate(const char *filename)
{
  FILE *out = fopen(filename, "w");
  if (!out) {
    err_sys("could not open '%s'", filename);
    exit(1);
  }

  int cycle_num = 0;
  int32_t branch = 0;
  int32_t ins;

cycle:
  int32_t fetch_executed = 0;
  int32_t ww = willwrite;
  int32_t wr = 0;
  int has_store = 0;

  /* Issue */
  for (int i = 0; i < 4 && (ins = pre_issue[i]); ++i) {
    switch (opcode(ins)) {
      case OP_sw:
        if (pre_alu1_ins2 || (ww | wr) & (1 << rs1(ins)) || ww & (1 << rs2(ins)) || has_store) {
          has_store = 1;
          wr |= (1 << rs1(ins)) | (1 << rs2(ins));
          continue;
        }
        pre_alu1_ins2 = ins;
        pre_alu1_addr2 = rget(rs2(ins)) + imm1(ins);
        pre_alu1_val2 = rget(rs1(ins));
        break;
      case OP_add:
      case OP_sub:
        if (pre_alu2_ins2 || pre_alu2_ins || (ww | wr) & (1 << rd(ins)) || ww & (1 << rs1(ins)) || ww & (1 << rs2(ins))) {
          ww |= 1 << rd(ins);
          wr |= (1 << rs1(ins)) | (1 << rs2(ins));
          continue;
        }
        pre_alu2_ins2 = ins;
        pre_alu2_lhs2 = rget(rs1(ins));
        pre_alu2_rhs2 = rget(rs2(ins));
        willwrite |= 1 << rd(ins);
        break;
      case OP_and:
      case OP_or:
        if (pre_alu3_ins2 || pre_alu3_ins || (ww | wr) & (1 << rd(ins)) || ww & (1 << rs1(ins)) || ww & (1 << rs2(ins))) {
          ww |= 1 << rd(ins);
          wr |= (1 << rs1(ins)) | (1 << rs2(ins));
          continue;
        }
        pre_alu3_ins2 = ins;
        pre_alu3_lhs2 = rget(rs1(ins));
        pre_alu3_rhs2 = rget(rs2(ins));
        willwrite |= 1 << rd(ins);
        break;
      case OP_addi:
        if (pre_alu2_ins2 || pre_alu2_ins || (ww | wr) & (1 << rd(ins)) || ww & (1 << rs1(ins))) {
          ww |= 1 << rd(ins);
          wr |= 1 << rs1(ins);
          continue;
        }
        pre_alu2_ins2 = ins;
        pre_alu2_lhs2 = rget(rs1(ins));
        pre_alu2_rhs2 = imm3(ins);
        willwrite |= 1 << rd(ins);
        break;
      case OP_andi:
      case OP_ori:
      case OP_sll:
      case OP_sra:
        if (pre_alu3_ins2 || pre_alu3_ins || (ww | wr) & (1 << rd(ins)) || ww & (1 << rs1(ins))) {
          ww |= 1 << rd(ins);
          wr |= 1 << rs1(ins);
          continue;
        }
        pre_alu3_ins2 = ins;
        pre_alu3_lhs2 = rget(rs1(ins));
        pre_alu3_rhs2 = imm3(ins);
        willwrite |= 1 << rd(ins);
        break;
      case OP_lw:
        if (pre_alu1_ins2 || (ww | wr) & (1 << rd(ins)) || ww & (1 << rs1(ins)) || has_store) {
          ww |= 1 << rd(ins);
          wr |= 1 << rs1(ins);
          continue;
        }
        pre_alu1_ins2 = ins;
        pre_alu1_addr2 = rget(rs1(ins)) + imm3(ins);
        willwrite |= 1 << rd(ins);
        break;
    }
    ww |= willwrite;
    for (int j = i; j < 3; ++j) {
      pre_issue[j] = pre_issue[j + 1];
    }
    pre_issue[3] = 0;
    --i;
  }

  /* Fetch/Decode */
  if (branch) {
    goto stop_fetch;
  }

  for (int i = 0; i < 2; ++i) {
    int slot = 0;
    while (pre_issue[slot]) {
      if (++slot == 4) {
        goto stop_fetch;
      }
    }
    int32_t ins = mem32(pc);
    pc += 4;
    switch (opcode(ins)) {
      case OP_beq:
      case OP_bne:
      case OP_blt:
        branch = ins;
        goto stop_fetch;
      case OP_sw:
      case OP_add:
      case OP_sub:
      case OP_and:
      case OP_or:
      case OP_addi:
      case OP_andi:
      case OP_ori:
      case OP_sll:
      case OP_sra:
      case OP_lw:
        pre_issue[slot] = ins;
        break;
      case OP_jal:
        rset(rd(ins), pc);
        pc = pc - 4 + (imm4(ins) << 1);
        fetch_executed = ins;
        goto stop_fetch;
      case OP_break:
        fetch_executed = ins;
        goto stop_fetch;
      default:
        err("invalid opcode %d", opcode(ins));
        exit(155);
    }
  }
stop_fetch:

  if (branch && !(ww & (1 << rs1(branch)) || ww & (1 << rs2(branch)))) {
    switch (opcode(branch)) {
      case OP_beq:
        if (rget(rs1(branch)) == rget(rs2(branch)))
          pc = pc - 4 + (imm1(branch) << 1);
        break;
      case OP_bne:
        if (rget(rs1(branch)) != rget(rs2(branch)))
          pc = pc - 4 + (imm1(branch) << 1);
        break;
      case OP_blt:
        if (rget(rs1(branch)) < rget(rs2(branch)))
          pc = pc - 4 + (imm1(branch) << 1);
        break;
    }
    fetch_executed = branch;
    branch = 0;
  }

  /* WB */
  if (post_mem_ins) {
    rset(rd(post_mem_ins), post_mem_val);
    post_mem_ins = 0;
  }
  if (post_alu2_ins) {
    rset(rd(post_alu2_ins), post_alu2_val);
    post_alu2_ins = 0;
  }
  if (post_alu3_ins) {
    rset(rd(post_alu3_ins), post_alu3_val);
    post_alu3_ins = 0;
  }

  /* MEM */
  if (pre_mem_ins) {
    switch (opcode(pre_mem_ins)) {
      case OP_lw:
        post_mem_ins = pre_mem_ins;
        post_mem_val = mem32(pre_mem_addr);
        break;
      case OP_sw:
        mem32(pre_mem_addr) = pre_mem_val;
        break;
    }
    pre_mem_ins = 0;
  }

  /* ALU3 */
  if (pre_alu3_ins) {
    switch (opcode(pre_alu3_ins)) {
      case OP_and:
      case OP_andi:
        post_alu3_val = pre_alu3_lhs & pre_alu3_rhs;
        break;
      case OP_or:
      case OP_ori:
        post_alu3_val = pre_alu3_lhs | pre_alu3_rhs;
        break;
      case OP_sll:
        post_alu3_val = pre_alu3_lhs << pre_alu3_rhs;
        break;
      case OP_sra:
        post_alu3_val = pre_alu3_lhs >> pre_alu3_rhs;
        break;
    }
    post_alu3_ins = pre_alu3_ins;
  }

  /* ALU2 */
  if (pre_alu2_ins) {
    switch (opcode(pre_alu2_ins)) {
      case OP_add:
      case OP_addi:
        post_alu2_val = pre_alu2_lhs + pre_alu2_rhs;
        break;
      case OP_sub:
        post_alu2_val = pre_alu2_lhs - pre_alu2_rhs;
        break;
    }
    post_alu2_ins = pre_alu2_ins;
  }

  /* ALU1 */
  if (pre_alu1_ins) {
    pre_mem_ins = pre_alu1_ins;
    pre_mem_addr = pre_alu1_addr;
    pre_mem_val = pre_alu1_val;
  }

  /* Issue */
  pre_alu1_ins = pre_alu1_ins2;
  pre_alu1_addr = pre_alu1_addr2;
  pre_alu1_val = pre_alu1_val2;
  pre_alu1_ins2 = 0;

  pre_alu2_ins = pre_alu2_ins2;
  pre_alu2_lhs = pre_alu2_lhs2;
  pre_alu2_rhs = pre_alu2_rhs2;
  pre_alu2_ins2 = 0;

  pre_alu3_ins = pre_alu3_ins2;
  pre_alu3_lhs = pre_alu3_lhs2;
  pre_alu3_rhs = pre_alu3_rhs2;
  pre_alu3_ins2 = 0;

  /* Print */
  ++cycle_num;

  fprintf(out,
    "--------------------\n"
    "Cycle %d:\n"
    "\n"
    "IF Unit:\n"
    ,
    cycle_num
  );

  fprintf(out, "\tWaiting:");
  print_instruction(out, branch);
  fprintf(out, "\tExecuted:");
  print_instruction(out, fetch_executed);
  fprintf(out, "Pre-Issue Queue:\n"
               "\tEntry 0:");
  print_instruction(out, pre_issue[0]);
  fprintf(out, "\tEntry 1:");
  print_instruction(out, pre_issue[1]);
  fprintf(out, "\tEntry 2:");
  print_instruction(out, pre_issue[2]);
  fprintf(out, "\tEntry 3:");
  print_instruction(out, pre_issue[3]);
  fprintf(out, "Pre-ALU1 Queue:\n"
               "\tEntry 0:");
  print_instruction(out, pre_alu1_ins);
  fprintf(out, "\tEntry 1:\n"
               "Pre-MEM Queue:");
  print_instruction(out, pre_mem_ins);
  fprintf(out, "Post-MEM Queue:");
  print_instruction(out, post_mem_ins);
  fprintf(out, "Pre-ALU2 Queue:");
  print_instruction(out, pre_alu2_ins);
  fprintf(out, "Post-ALU2 Queue:");
  print_instruction(out, post_alu2_ins);
  fprintf(out, "Pre-ALU3 Queue:");
  print_instruction(out, pre_alu3_ins);
  fprintf(out, "Post-ALU3 Queue:");
  print_instruction(out, post_alu3_ins);
  fprintf(out,
    "\n"
    "Registers\n"
    "x00:\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n"
    "x08:\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n"
    "x16:\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n"
    "x24:\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n"
    "Data"
    ,
    regs[0],  regs[1],  regs[2],  regs[3],  regs[4],  regs[5],  regs[6],  regs[7],
    regs[8],  regs[9],  regs[10], regs[11], regs[12], regs[13], regs[14], regs[15],
    regs[16], regs[17], regs[18], regs[19], regs[20], regs[21], regs[22], regs[23],
    regs[24], regs[25], regs[26], regs[27], regs[28], regs[29], regs[30], regs[31]
  );
  for (int32_t addr = mem_data; addr < mem_end; addr += 4) {
    if (!((addr - mem_data) & 31)) {
      fprintf(out, "\n%d:", addr);
    }
    fprintf(out, "\t%d", mem32(addr));
  }
  fputc('\n', out);

  if (opcode(fetch_executed) != OP_break) {
    goto cycle;
  }

  fclose(out);
}

int main(int argc, char **argv)
{
  if (argc != 2) {
    err("expected one filename argument");
    return 2;
  }

  program_load(argv[1]);
  program_simulate("simulation.txt");
  return 0;
}

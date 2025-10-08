#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define MEM32(mem, addr) (*(int32_t *)((char *)(mem) + (addr) - 256))

static const char *const disassembly_filename = "disassembly.txt";
static const char *const simulation_filename = "simulation.txt";

struct program
{
  uint32_t regs[32];
  uint32_t pc;
  uint32_t mem_size;
  uint32_t mem_lower;
  uint32_t mem_data;
  uint32_t mem_upper;
  void *mem;
};

static void write_bin32(FILE *out, uint32_t word)
{
  char bin[32];
  for (int i = 0; i < 32; i++) {
    bin[i] = '0' + (word >> (31 - i) & 1);
  }
  fwrite(bin, sizeof(bin), 1, out);
}

static void err(const char *format, ...)
{
  va_list ap;
  fputs("error: ", stderr);
  va_start(ap, format);
  vfprintf(stderr, format, ap);
  va_end(ap);
  fputc('\n', stderr);
}

static void err_sys(const char *format, ...)
{
  va_list ap;
  fputs("error: ", stderr);
  va_start(ap, format);
  vfprintf(stderr, format, ap);
  va_end(ap);
  fprintf(stderr, ": %s\n", strerror(errno));
}

static int init_program_from_fd(struct program *program, int fd)
{

  struct stat st;
  if (fstat(fd, &st)) {
    err_sys("fstat");
    return -1;
  }

  uint32_t max_mem_size = st.st_size / 8;
  void *mem = calloc(1, max_mem_size);
  if (!mem) {
    err("failed to allocate program memory");
    return -1;
  }

  char buffer[1024];
  int bitcount = 0;
  uint32_t word = 0;
  uint32_t mem_size = 0;
  uint32_t mem_data = 0;

  while (1) {
    char *cur, *end;
    ssize_t len = read(fd, buffer, sizeof(buffer));
    if (len < 0) {
      err_sys("read");
      free(mem);
      return -1;
    }
    if (len == 0) {
      break;
    }
    end = buffer + len;
    for (cur = buffer; cur < end; cur++) {
      if (*cur == '0') {
        word = word << 1;
      } else if (*cur == '1') {
        word = word << 1 | 1;
      } else {
        continue;
      }
      if (++bitcount < 32) {
        continue;
      }
      uint32_t addr = mem_size + 256;
      MEM32(mem, addr) = word;
      /* detect break */
      if (!mem_data && word == 127) {
        mem_data = addr + 4;
      }
      bitcount = 0;
      word = 0;
      mem_size += 4;
    }
  }

  if (!mem_data) {
    err("no break instruction found");
    free(mem);
    return -1;
  }

  memset(program, 0, sizeof(*program));
  program->pc = 256;
  program->mem_size = mem_size;
  program->mem_lower = 256;
  program->mem_data = mem_data;
  program->mem_upper = mem_size + 256;
  program->mem = mem;
  return 0;
}

static int init_program(struct program *program, const char *filename)
{
  int fd = open(filename, O_RDONLY);
  if (fd < 0) {
    err_sys("failed to open '%s'", filename);
    return -1;
  }
  int ret = init_program_from_fd(program, fd);
  close(fd);
  return ret;
}

static void process_instruction(FILE *out, struct program *program,
    uint32_t ins, uint32_t addr)
{
  unsigned int rs1, rs2, rd;
  int imm;
  switch (ins & 3) {
    /* Category-1 */
    case 0:
      rs1 = ins >> 15 & 31;
      rs2 = ins >> 20 & 31;
      imm = (ins >> 7 & 31) | ((int32_t)ins >> 20 & ~31);
      switch (ins >> 2 & 31) {
        /* beq rs1, rs2, #imm */
        case 0:
          fprintf(out, "beq x%u, x%u, #%d", rs1, rs2, imm);
          if (program && program->regs[rs1] == program->regs[rs2]) {
            program->pc = addr + (imm << 1);
          }
          return;
        /* bne rs1, rs2, #imm */
        case 1:
          fprintf(out, "bne x%u, x%u, #%d", rs1, rs2, imm);
          if (program && program->regs[rs1] != program->regs[rs2]) {
            program->pc = addr + (imm << 1);
          }
          return;
        /* blt rs1, rs2, #imm */
        case 2:
          fprintf(out, "blt x%u, x%u, #%d", rs1, rs2, imm);
          if (program && (int32_t)program->regs[rs1] < (int32_t)program->regs[rs2]) {
            program->pc = addr + (imm << 1);
          }
          return;
        /* sw rs1, imm(rs2) */
        case 3:
          fprintf(out, "sw x%u, %d(x%u)", rs1, imm, rs2);
          if (program) {
            MEM32(program->mem, program->regs[rs2] + imm) = program->regs[rs1];
          }
          return;
      }
      break;
    /* Category-2 */
    case 1:
      rd = ins >> 7 & 31;
      rs1 = ins >> 15 & 31;
      rs2 = ins >> 20 & 31;
      switch (ins >> 2 & 31) {
        /* add rd, rs1, rs2 */
        case 0:
          fprintf(out, "add x%u, x%u, x%u", rd, rs1, rs2);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] + program->regs[rs2];
          }
          return;
        /* sub rd, rs1, rs2 */
        case 1:
          fprintf(out, "sub x%u, x%u, x%u", rd, rs1, rs2);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] - program->regs[rs2];
          }
          return;
        /* and rd, rs1, rs2 */
        case 2:
          fprintf(out, "and x%u, x%u, x%u", rd, rs1, rs2);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] & program->regs[rs2];
          }
          return;
        /* or rd, rs1, rs2 */
        case 3:
          fprintf(out, "or x%u, x%u, x%u", rd, rs1, rs2);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] | program->regs[rs2];
          }
          return;
      }
      break;
    /* Category-3 */
    case 2:
      rd = ins >> 7 & 31;
      rs1 = ins >> 15 & 31;
      imm = (int32_t)ins >> 20;
      switch (ins >> 2 & 31) {
        /* addi rd, rs1, #imm */
        case 0:
          fprintf(out, "addi x%u, x%u, #%d", rd, rs1, imm);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] + imm;
          }
          return;
        /* andi rd, rs1, #imm */
        case 1:
          fprintf(out, "andi x%u, x%u, #%d", rd, rs1, imm);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] & imm;
          }
          return;
        /* ori rd, rs1, #imm */
        case 2:
          fprintf(out, "ori x%u, x%u, #%d", rd, rs1, imm);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] | imm;
          }
          return;
        /* sll rd, rs1, #imm */
        case 3:
          fprintf(out, "sll x%u, x%u, #%d", rd, rs1, imm);
          if (program && rd) {
            program->regs[rd] = program->regs[rs1] << imm;
          }
          return;
        /* sra rd, rs1, #imm */
        case 4:
          fprintf(out, "sra x%u, x%u, #%d", rd, rs1, imm);
          if (program && rd) {
            program->regs[rd] = (int32_t)program->regs[rs1] >> imm;
          }
          return;
        /* lw rd, imm(rs1) */
        case 5:
          fprintf(out, "lw x%u, %d(x%u)", rd, imm, rs1);
          if (program && rd) {
            program->regs[rd] = MEM32(program->mem, program->regs[rs1] + imm);
          }
          return;
      }
      break;
    /* Category-4 */
    case 3:
      rd = ins >> 7 & 31;
      imm = (int32_t)ins >> 12;
      switch (ins >> 2 & 31) {
        /* jal rd, #imm */
        case 0:
          fprintf(out, "jal x%u, #%d", rd, imm);
          if (program) {
            if (rd) {
              program->regs[rd] = program->pc;
            }
            program->pc = addr + (imm << 1);
          }
          return;
        /* break */
        case 31:
          fprintf(out, "break");
          if (program) {
            program->pc = 0;
          }
          return;
      }
      break;
  }
  fprintf(out, "invalid");
}

static void disassemble_to(FILE *out, struct program *program)
{
  for (uint32_t addr = program->mem_lower; addr < program->mem_upper; addr += 4) {
    uint32_t word = MEM32(program->mem, addr);
    write_bin32(out, word);
    fprintf(out, "\t%" PRIu32 "\t", addr);
    if (addr < program->mem_data) {
      process_instruction(out, NULL, word, addr);
    } else {
      fprintf(out, "%" PRId32, (int32_t)word);
    }
    fputc('\n', out);
  }
}

static int disassemble(const char *filename, struct program *program)
{
  FILE *file = fopen(filename, "w");
  if (!file) {
    err_sys("failed to open '%s'", filename);
    return 1;
  }
  disassemble_to(file, program);
  fclose(file);
  return 0;
}

static void simulate_to(FILE *out, struct program *program)
{
  unsigned int counter = 0;
  uint32_t data_size = program->mem_upper - program->mem_data;
  while (program->pc) {
    uint32_t addr = program->pc;
    uint32_t ins = MEM32(program->mem, addr);
    ++counter;
    fprintf(out,
        "--------------------\n"
        "Cycle %u:\t%"PRIu32"\t"
        , counter, addr);
    program->pc += 4;
    process_instruction(out, program, ins, addr);
    fprintf(out, "\nRegisters");
    for (unsigned int r = 0; r < 32; r++) {
      if ((r & 7) == 0) {
        fprintf(out, "\nx%02u:", r);
      }
      fprintf(out, "\t%"PRId32, (int32_t)program->regs[r]);
    }
    fprintf(out, "\nData");
    for (uint32_t offset = 0; offset < data_size; offset += 4) {
      uint32_t mem_addr = program->mem_data + offset;
      if ((offset & 31) == 0) {
        fprintf(out, "\n%"PRIu32":", mem_addr);
      }
      fprintf(out, "\t%"PRId32, MEM32(program->mem, mem_addr));
    }
    fputc('\n', out);
  }
}

static int simulate(const char *filename, struct program *program)
{
  FILE *file = fopen(filename, "w");
  if (!file) {
    err_sys("failed to open '%s'", filename);
    return 1;
  }
  simulate_to(file, program);
  fclose(file);
  return 0;
}

int main(int argc, char **argv)
{
  if (argc < 2) {
    fprintf(stderr, "usage: Vsim <input>\n");
    return 2;
  }

  struct program program;
  if (init_program(&program, argv[1])) {
    return 1;
  }

  disassemble(disassembly_filename, &program);
  simulate(simulation_filename, &program);
  return 0;
}

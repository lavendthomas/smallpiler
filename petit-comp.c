/* fichier: "petit-comp.c" */

/* Un petit compilateur et machine virtuelle pour un sous-ensemble de C.  */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*---------------------------------------------------------------------------*/

/* Analyseur lexical. */

enum { DO_SYM, ELSE_SYM, IF_SYM, WHILE_SYM, PRINT_SYM, CONTINUE_SYM, BREAK_SYM, LBRA, RBRA, LPAR,
       RPAR, PLUS, MINUS, LESS, LEQ, GREATER, GEQ, SEMI, EQUAL, INT, ID, EOI,
       TIMES, OVER, MODULO};

char *words[] = { "do", "else", "if", "while", "print", "continue", "break", NULL };

int ch = ' ';
int sym;
int int_val;
char id_name[100];

void syntax_error() { fprintf(stderr, "syntax error\n"); exit(1); }

void next_ch() { ch = getchar(); }

void next_sym()
{
  while (ch == ' ' || ch == '\n') next_ch();
  switch (ch)
    { case '{': sym = LBRA;    next_ch(); break;
      case '}': sym = RBRA;    next_ch(); break;
      case '(': sym = LPAR;    next_ch(); break;
      case ')': sym = RPAR;    next_ch(); break;
      case '+': sym = PLUS;    next_ch(); break;
      case '-': sym = MINUS;   next_ch(); break;
      case '*': sym = TIMES;   next_ch(); break;
      case '/': sym = OVER;    next_ch(); break;
      case '%': sym = MODULO;  next_ch(); break;
      case '<': {
          sym = LESS;
          next_ch();
          if (ch == '=') {
              sym = LEQ;
              next_ch();
          }
          break;
      }
      case '>': {
          sym = GREATER;
          next_ch();
          if (ch == '=') {
              sym = GEQ;
              next_ch();
          }
          break;
      }
      case ';': sym = SEMI;    next_ch(); break;
      case '=': sym = EQUAL;   next_ch(); break;
      case EOF: sym = EOI;     next_ch(); break;
      default:
          if (ch >= '0' && ch <= '9') {
              int_val = 0; /* overflow? */

              while (ch >= '0' && ch <= '9') {
                  int_val = int_val * 10 + (ch - '0');
                  next_ch();
              }
              sym = INT;
          } else if (ch >= 'a' && ch <= 'z') {
              int i = 0; /* overflow? */



              while ((ch >= 'a' && ch <= 'z') || ch == '_') {
                  id_name[i++] = ch;
                  next_ch();
              }

              id_name[i] = '\0';
              sym = 0;

              while (words[sym] != NULL && strcmp(words[sym], id_name) != 0)
                  sym++;

              if (words[sym] == NULL) {
                  if (id_name[1] == '\0') sym = ID; else syntax_error();
              }
          } else syntax_error();
    }
}

/*---------------------------------------------------------------------------*/

/* Analyseur syntaxique. */

enum { VAR, CST, ADD, SUB, LT, GT, LE, GE, ASSIGN,
       IF1, IF2, WHILE, DO, EMPTY, SEQ, EXPR, PROG,
       MULT, DIV10, MOD10, PRINT, BREAK, CONTINUE};


#define POSITIVE 0
#define NEGATIVE -1

#define MOD(a,b) ((a) % (b) + (b)) %(b);        // https://stackoverflow.com/a/42131603

typedef signed char code;


typedef struct big_integer {
    int count;              // Number of links to the big_integer (<= 26-> No overflow)
    int sign;               // 0 for +, something else for -
    struct cell *digits;

} big_integer;

typedef struct cell {
    char digit;
    struct cell *next;
} cell;

big_integer *new_integer(int value) {
    big_integer *nb = malloc(sizeof(big_integer));
    if (nb == NULL) {
        //TODO better error handling : Not enough memory
        syntax_error();
    }
    nb->count = 1;
    if (value >= 0) {
        nb->sign = POSITIVE;
    } else {
        nb->sign = NEGATIVE;
        value = -value;             // Get the absolute value of value.
    }

    if (value == 0) {
        nb->digits = NULL;
    } else {
        int modulo = 10;
        cell *prev = NULL;
        cell *first;
        while (value != 0) {

            // Get the digit at position modulo
            int digit = value % modulo;
            value /= modulo;

            // Add node to the big_integer
            cell *cell = malloc(sizeof(cell));
            if (cell == NULL) {
                //TODO better error handling : Not enough memory
                syntax_error();
            }
            cell->next = NULL;
            if (prev != NULL) {
                prev->next = cell;
            } else {
                // If it has no previous node, then it's the first one
                first = cell;
            }
            cell->digit = digit;
            prev = cell;
        }
        nb->digits = first;
    }
    return nb;
}

/**
 * Frees the memory used by the cell n and all the following cells it points to.
 * @param n
 */
void _big_integer_cell_free(cell *n) {
    if (n != NULL) {
        _big_integer_cell_free(n->next);
        free(n);
    }
}

/**
 * Call this function when you won't use your pointer to this big_integer.
 *
 * The memory used by this number will be freed if no other pointer uses this big_integer.
 * @param n
 */
void big_integer_free(big_integer *n) {
    if (n != NULL) {
        if (n->count > 1) {
            n->count = n->count - 1;
        } else {
            // The big_integer will not be used. Free its memory
            _big_integer_cell_free(n->digits);
            free(n);
        }
    }
}

void _big_integer_print(cell *c) {
    if (c != NULL && c->next != NULL) {
        _big_integer_print(c->next);
    }
    putchar( c->digit + '0');
}

void big_integer_print(big_integer *nb) {
    if (nb == NULL) {
        return;
    }
    if (nb->digits == NULL) {
        putchar( '0');
        return;
    }
    if (nb->sign == NEGATIVE) {
        putchar('-');
    }
    _big_integer_print(nb->digits);
}

/**
 * Returns the number of digits of a big integer.
 *
 * WARNING : overflows if the number of digits in base 10 is higher than or
 *           equal to INT_MAX
 */
int big_integer_size(big_integer *integer) {
    int size = 0;
    cell *this = integer->digits;
    while (this != NULL) {
        size++;
        this = this->next;
    }
    return size;
}


/**
 *  Returns a new big_integer containing the sum of the two integers in parameters.
 */
big_integer *big_integer_sum(big_integer *bi1, big_integer *bi2) {
    big_integer *sum = new_integer(0);

    cell *d1 = bi1->digits;
    cell *d2 = bi2->digits;
    int sign, sign1, sign2;
    cell *first = NULL, *prev = NULL;
    int carry = 0;

    sign1 = (bi1->sign == POSITIVE) ? POSITIVE : NEGATIVE;
    sign2 = (bi2->sign == POSITIVE) ? POSITIVE : NEGATIVE;

    // Do like in primary school

    while (d1 != NULL || d2 != NULL || carry != 0 ) {
        int s = carry;
        sign = (sign1 == NEGATIVE && sign2 == NEGATIVE) ? NEGATIVE : POSITIVE;
        if (d1 != NULL) {
            if (sign1 == POSITIVE) {
                s += d1->digit;
            } else {
                s -= d1->digit;
                if (d2 == NULL) {
                    // We substract more digits than there are positive digits
                    sign = NEGATIVE;
                }
            }
        }
        if (d2 != NULL) {
            if (sign2 == POSITIVE) {
                s += d2->digit;
            } else {
                s -= d2->digit;
                if (d1 == NULL) {
                    // We substract more digits than there are positive digits
                    sign = NEGATIVE;
                }
            }

        }

        if (d1 != NULL) {
            d1 = d1->next;
        }
        if (d2 != NULL) {
            d2 = d2->next;
        }



        if (s >= 10) {       // carry = s // 10 in Python, carry = s / 10 doesn't work
            carry = 1;
        } else if (s < 0) {
            carry = -1;

        } else {
            carry = 0;
        }

        if (carry < 0 &&( (sign1 == POSITIVE && d1 == NULL) || (sign2 == POSITIVE && d2 == NULL)) ) {
            big_integer *x;
            // the sum is negative
            /* sign = NEGATIVE;
            carry = 1;
            s = 10 - s;*/
            bi1->sign = (bi1->sign == POSITIVE) ? NEGATIVE : POSITIVE;
            bi2->sign = (bi2->sign == POSITIVE) ? NEGATIVE : POSITIVE;
            x = big_integer_sum(bi2, bi1);
            x->sign = (x->sign == POSITIVE) ? NEGATIVE : POSITIVE;
            // put the correct sign bach
            bi1->sign = (bi1->sign == POSITIVE) ? NEGATIVE : POSITIVE;
            bi2->sign = (bi2->sign == POSITIVE) ? NEGATIVE : POSITIVE;

            sum->digits = first;
            _big_integer_cell_free(sum);        // Free the previous instance we created but will never use

            return x;
        }
        s = MOD(s,10);

        cell *new_cell = malloc(sizeof(cell));

        if (new_cell == NULL) {
            //TODO better error handling : Not enough memory
            syntax_error();
        }

        new_cell->digit = s;
        new_cell->next = NULL;

        if (prev != NULL) {
            prev->next = new_cell;
        } else {
            first = new_cell;
        }
        prev = new_cell;
    }

    sum->digits = first;
    sum->sign = sign;

    return sum;
}

/**
* Returns a pointer to a copy of a
*/
big_integer *big_integer_copy(big_integer *a) {
 if (a != NULL) {
     big_integer *cp = new_integer(0);
     cell *prev = NULL, *first = NULL;
     cell *current = a->digits;
     cp->sign = a->sign;

     while (current != NULL) {
         cell *c = malloc(sizeof(cell));

         if (c == NULL) {
             //TODO better error handling : Not enough memory
             syntax_error();
         }

         c->next = NULL;
         if (prev != NULL) {
             prev->next = c;
         } else {
             // If it has no previous node, then it's the first one
             first = c;
         }
         c->digit = current->digit;
         prev = c;
     }
     cp->digits = first;
 }
}


/**
 *  Returns a pointer to new big_integer with 10 * nb.
 */
big_integer *big_integer_multiply(big_integer *a, big_integer *b) {
    // Copy if useful
    if (a != NULL && b != NULL) {
        if (a->digits == NULL || b->digits == NULL) {
            return new_integer(0);
        } else {

            big_integer *product = new_integer(0);

            int pow = 0;
            big_integer *term;

            cell *cur_b = b->digits;

            while (cur_b != NULL) {
                cell *cur_a = a->digits;
                int carry = 0;
                cell *prev = NULL;
                term = new_integer(0);
                while (cur_a != NULL || carry != 0) {
                    cell *c = malloc(sizeof(cell));
                    if (c == NULL) {
                        // TODO better handle out of memory
                        syntax_error();
                    }
                    int value;
                    if (cur_a != NULL) {
                        value = cur_a->digit * cur_b->digit + carry;
                    } else {
                        value = carry; // No digits left
                    }


                    carry = value / 10;     // We can use standard C divmod because all numbers
                    value = value % 10;     // wil always be positive
                    c->digit = value;

                    if (prev != NULL) {
                        prev->next = c;
                    } else {
                        term->digits = c;
                    }

                    prev = c;
                    if (cur_a != NULL) cur_a = cur_a->next;
                }

                // We add pow trailing zeros

                int j;
                for (j=0; j<pow; j++) {
                    cell *zero = malloc(sizeof(cell));
                    if (zero == NULL) {
                        // Better handle out of memory
                        syntax_error();
                    }
                    zero->digit = 0;
                    zero->next = term->digits;
                    term->digits = zero;
                }

                pow++;
                cur_b = cur_b->next;

                // Add the term to the big sum
                big_integer *old_product = product;
                product = big_integer_sum(old_product, term);

                big_integer_free(old_product);  // Free memory for temporary variables on heap
                big_integer_free(term);
            }
            product->sign = (a->sign == b->sign) ? POSITIVE : NEGATIVE;
            return product;
        }

    } else {
        return NULL;
    }
}

/**
 *  Returns a new pointer to a big_integer containing a/10.
 */
big_integer *big_integer_divide(big_integer *a) {
    big_integer *b = big_integer_copy(a);       // Return a copy

    if (b != NULL) {
        if (b->digits != NULL) {
            // There are digits, so nb != 0 => remove last digit ans free its memory
            cell *last = b->digits;
            b->digits = last->next;
            free(last);
        }

        return  b;
    } else {
        return NULL;
    }
}

/**
 * Returns a pointer to a new big_integer containing a % 10
 */
big_integer *big_integer_modulo(big_integer *a) {
    if (a != NULL) {
        if (a->digits == NULL) {
            return new_integer(0);
        } else {
            return new_integer(a->digits->digit);
        }
    }
}

/**
 *  Returns a new big_integer containing the difference of the two integers in parameters.
 */
big_integer *big_integer_difference(big_integer *bi1, big_integer *bi2) {
    big_integer *diff;
    if (bi2->sign == POSITIVE) {                // Should be make a copy to support embedded calls ?
        bi2->sign = NEGATIVE;
        diff = big_integer_sum(bi1, bi2);
        bi2->sign = POSITIVE;
    } else {
        bi2->sign = POSITIVE;
        diff = big_integer_sum(bi1, bi2);
        bi2->sign = NEGATIVE;
    }
    return diff;
}


/**
 * Returns 0 if and only if n != 0
 */
int big_integer_is_zero(big_integer *n) {
    if (n != NULL) {
        return n->digits == NULL;
    } else {
        //TODO better nullpointerexception
        syntax_error();
        return 0;
    }
}

/**
 * Returns 0 if and only if n > 0
 */
int big_integer_is_positive(big_integer *n) {
    if (n != NULL) {
        return n->digits != NULL && n->sign == POSITIVE;
    } else {
        //TODO better nullpointerexception
        syntax_error();
        return 0;
    }
}

/**
 * Returns 0 if and only if n > 0
 */
int big_integer_is_negative(big_integer *n) {
    if (n != NULL) {
        return n->digits != NULL && n->sign == NEGATIVE;
    } else {
        //TODO better nullpointerexception
        syntax_error();
        return 0;
    }
}



union val {
    int variable;
    big_integer *integer;
} ;

struct node
  {
    int kind;
    struct node *o1;
    struct node *o2;
    struct node *o3;
    union val val;
  };

typedef struct node node;

node *new_node(int k)
{
  node *x = malloc(sizeof(node));
  if (x == NULL) {
      //TODO handle better
      syntax_error();
  }
  x->kind = k;
  return x;
}

node *paren_expr(); /* forward declaration */

node *term() /* <term> ::= <id> | <int> | <paren_expr> */
{
  node *x;

  if (sym == ID)           /* <term> ::= <id> */
    {
      x = new_node(VAR);
      x->val.variable = id_name[0]-'a';
      next_sym();
    }
  else if (sym == INT)     /* <term> ::= <int> */
    {
      x = new_node(CST);
      x->val.integer = new_integer(int_val);
      next_sym();
    }
  else                     /* <term> ::= <paren_expr> */
    x = paren_expr();

  return x;
}

node *mult() {
    node *x = term();

    while (sym == TIMES || sym == OVER || sym == MODULO) {
        node *t = x;
        switch (sym) {
            case TIMES   : x = new_node(MULT); break;
            case OVER  : x = new_node(DIV10); break;
            case MODULO : x = new_node(MOD10); break;
        }
        if (sym == OVER || sym == MODULO) {
            // TODO check that the right term is a constant containing 10.
        }
        next_sym();
        x->o1 = t;
        x->o2 = term();
    }
    return x;
}


node *sum() /* <sum> ::= <mult>|<sum>"+"<mult>|<sum>"-"<mult> */
{
  node *x = mult();

  while (sym == PLUS || sym == MINUS)
    {
      node *t = x;
      x = new_node(sym==PLUS ? ADD : SUB);
      next_sym();
      x->o1 = t;
      x->o2 = mult();
    }

  return x;
}

node *test() /* <test> ::= <sum> | <sum> "<" <sum> */
{
  node *x = sum();

    if (sym == LESS) {
        node *t = x;
        x = new_node(LT);
        next_sym();
        x->o1 = t;
        x->o2 = sum();
    } else if (sym == GREATER) {
        node *t = x;
        x = new_node(GT);
        next_sym();
        x->o1 = t;
        x->o2 = sum();
    } else if (sym == LEQ) {
        node *t = x;
        x = new_node(LE);
        next_sym();
        x->o1 = t;
        x->o2 = sum();
    } else if (sym == GEQ) {
        node *t = x;
        x = new_node(GE);
        next_sym();
        x->o1 = t;
        x->o2 = sum();
    }

  return x;
}

node *expr() /* <expr> ::= <test> | <id> "=" <expr> */
{
  node *x;

  if (sym != ID) return test();

  x = test();

  if (sym == EQUAL)
    {
      node *t = x;
      x = new_node(ASSIGN);
      next_sym();
      x->o1 = t;
      x->o2 = expr();
    }

  return x;
}

node *paren_expr() /* <paren_expr> ::= "(" <expr> ")" */
{
  node *x;

  if (sym == LPAR) next_sym(); else syntax_error();

  x = expr();

  if (sym == RPAR) next_sym(); else syntax_error();

  return x;
}

node *statement()
{
  node *x;

  if (sym == IF_SYM)       /* "if" <paren_expr> <stat> */
    {
      x = new_node(IF1);
      next_sym();
      x->o1 = paren_expr();
      x->o2 = statement();
      if (sym == ELSE_SYM) /* ... "else" <stat> */
        { x->kind = IF2;
          next_sym();
          x->o3 = statement();
        }
    }
  else if (sym == WHILE_SYM) /* "while" <paren_expr> <stat> */
    {
      x = new_node(WHILE);
      next_sym();
      x->o1 = paren_expr();
      x->o2 = statement();
    }
  else if (sym == DO_SYM)  /* "do" <stat> "while" <paren_expr> ";" */
    {
      x = new_node(DO);
      next_sym();
      x->o1 = statement();
      if (sym == WHILE_SYM) next_sym(); else syntax_error();
      x->o2 = paren_expr();
      if (sym == SEMI) next_sym(); else syntax_error();
    }
  else if (sym == SEMI)    /* ";" */
    {
      x = new_node(EMPTY);
      next_sym();
    }
  else if (sym == LBRA)    /* "{" { <stat> } "}" */
    {
      x = new_node(EMPTY);
      next_sym();
      while (sym != RBRA)
        {
          node *t = x;
          x = new_node(SEQ);
          x->o1 = t;
          x->o2 = statement();
        }
      next_sym();
    }
  else if (sym == PRINT_SYM) {
      x = new_node(PRINT);
      next_sym();
      x->o1 = paren_expr();

      if (sym == SEMI) {
          next_sym();
      } else {
          syntax_error();
      }

  } else if  (sym == BREAK_SYM)  {     /*  "break" ";" */

      x = new_node(BREAK);
      if (sym == SEMI) next_sym(); else syntax_error();

  } else if  (sym == CONTINUE_SYM)  {     /*  "continue" ";" */

      x = new_node(CONTINUE);
      if (sym == SEMI) next_sym(); else syntax_error();

  } else {         /* <expr> ";" */

      x = new_node(EXPR);
      x->o1 = expr();
      if (sym == SEMI) next_sym(); else syntax_error();

  }

  return x;
}

node *program()  /* <program> ::= <stat> */
{
  node *x = new_node(PROG);
  next_sym();
  x->o1 = statement();
  if (sym != EOI) syntax_error();
  return x;
}

/*---------------------------------------------------------------------------*/

/* Generateur de code. */

enum { ILOAD, ISTORE, BIPUSH, DUP, POP, IADD, ISUB,
       GOTO, IFEQ, IFNE, IFLT, RETURN,
       PRNT, IFLE, IFGE, IFGT,
       BGLOAD, BGSTORE, BGPUSH, BGPOP,
       BGADD, BGSUB, BGDUP,
       BGMULT, BGDIV, BGMOD};

#define BIG_INTEGER_LIMITER 127             // digits < 10



code object[1000], *here = object;

void gen(code c) { *here++ = c; } /* overflow? */

#ifdef SHOW_CODE
#define g(c) do { printf(" %d",c); gen(c); } while (0)
#define gi(c) do { printf("\n%s", #c); gen(c); } while (0)
#else
#define g(c) gen(c)
#define gi(c) gen(c)
#endif

void fix(code *src, code *dst) { *src = dst-src; } /* overflow? */

void c(node *x) {
    switch (x->kind) {
        case VAR   :
            gi(ILOAD);
            g(x->val.variable);
            break;

        case CST   :
            gi(BGPUSH);
            g(x->val.integer->sign);
            cell *digit = x->val.integer->digits;
            while (digit != NULL) {
                g(digit->digit);
                digit = digit->next;
            }
            g(BIG_INTEGER_LIMITER);
            // TODO should we free the big_integer here?
            break;
        case ADD   :
            c(x->o1);
            c(x->o2);
            gi(BGADD);
            break;

        case SUB   :
            c(x->o1);
            c(x->o2);
            gi(BGSUB);
            break;

        case MULT   :
            c(x->o1);
            c(x->o2);
            gi(BGMULT);
            break;

        case LT    :
            gi(BGPUSH);
            g(POSITIVE);        // Push 1 to the stack
            g(1);
            g(BIG_INTEGER_LIMITER);
            c(x->o1);
            c(x->o2);
            gi(BGSUB);
            gi(IFLT);
            g(5);       // jump 5 bytes (-> break)
            gi(BGPOP);
            gi(BGPUSH);
            g(POSITIVE);        // Push 0 to the stack
            g(BIG_INTEGER_LIMITER);
            break;

        case LE     :
            gi(BGPUSH);
            g(POSITIVE);        // Push 1 to the stack
            g(1);
            g(BIG_INTEGER_LIMITER);
            c(x->o1);
            c(x->o2);
            gi(BGSUB);
            gi(IFLE);
            g(5);       // jump 5 bytes (-> break)
            gi(BGPOP);
            gi(BGPUSH);
            g(POSITIVE);        // Push 0 to the stack
            g(BIG_INTEGER_LIMITER);
            break;


        case GT     :
            gi(BGPUSH);
            g(POSITIVE);        // Push 1 to the stack
            g(1);
            g(BIG_INTEGER_LIMITER);
            c(x->o1);
            c(x->o2);
            gi(BGSUB);
            gi(IFGT);
            g(5);       // jump 5 bytes (-> break)
            gi(BGPOP);
            gi(BGPUSH);
            g(POSITIVE);        // Push 0 to the stack
            g(BIG_INTEGER_LIMITER);
            break;

        case GE     :
            gi(BGPUSH);
            g(POSITIVE);        // Push 1 to the stack
            g(1);
            g(BIG_INTEGER_LIMITER);
            c(x->o1);
            c(x->o2);
            gi(BGSUB);
            gi(IFGE);
            g(5);       // jump 5 bytes (-> break)
            gi(BGPOP);
            gi(BGPUSH);
            g(POSITIVE);        // Push 0 to the stack
            g(BIG_INTEGER_LIMITER);
            break;

        case ASSIGN: // Replace by globals[i] = globals[j] in virtual machine
            c(x->o2);
            gi(BGDUP);
            gi(BGSTORE);
            g(x->o1->val.variable);
            break;

        case IF1   : {
            code *p1;
            c(x->o1);
            gi(IFEQ);
            p1 = here++;
            c(x->o2);
            fix(p1, here);
            break;
        }

        case IF2   : {
            code *p1, *p2;
            c(x->o1);
            gi(IFEQ);
            p1 = here++;
            c(x->o2);
            gi(GOTO);
            p2 = here++;
            fix(p1, here);
            c(x->o3);
            fix(p2, here);
            break;
        }

        case WHILE : {
            code *p1 = here, *p2;
            c(x->o1);
            gi(IFEQ);
            p2 = here++;
            c(x->o2);
            gi(GOTO);
            fix(here++, p1);
            fix(p2, here);
            break;
        }

        case DO    : {
            code *p1 = here;
            c(x->o1);
            c(x->o2);
            gi(IFNE);
            fix(here++, p1);
            break;
        }

        case EMPTY :
            break;

        case SEQ   :
            c(x->o1);
            c(x->o2);
            break;

        case EXPR  :
            c(x->o1);
            gi(POP);
            break;

        case PROG  :
            c(x->o1);
            gi(RETURN);
            break;
    }
}

/*---------------------------------------------------------------------------*/

/* Machine virtuelle. */

typedef struct linked_list linked_list;

struct linked_list {
    code data;
    linked_list *next;
} ;

long globals[26];

void run()
{
  long stack[1000], *sp = stack; /* overflow? */
  code *pc = object;

  for (;;)
    switch (*pc++)
      {
        case ILOAD : *sp++ = globals[*pc++];             break;
        case ISTORE: globals[*pc++] = *--sp;             break;
        case BIPUSH: *sp++ = *pc++;                      break;
        case DUP   : sp++; sp[-1] = sp[-2];              break;
        case POP   : --sp;                               break;
        case IADD  : sp[-2] = sp[-2] + sp[-1]; --sp;     break;
        case ISUB  : sp[-2] = sp[-2] - sp[-1]; --sp;     break;
        case GOTO  : pc += *pc;                          break;
        case IFEQ  : if (big_integer_is_zero((big_integer *) *(--sp))) pc += *pc; else pc++;        break;
        case IFNE  : if (!big_integer_is_zero((big_integer *) *(--sp))) pc += *pc; else pc++;       break;
        case IFLT  : if (big_integer_is_negative((big_integer *) *(--sp))) pc += *pc; else pc++;    break;
        case IFLE  : {
            big_integer *nb = (big_integer *) *(--sp);
            if (big_integer_is_negative(nb) || big_integer_is_zero(nb)) pc += *pc; else pc++;    break;
        }
          case IFGT  : if (big_integer_is_positive((big_integer *) *(--sp))) pc += *pc; else pc++;    break;
        case IFGE  : {
            big_integer *nb = (big_integer *) *(--sp);
            if (big_integer_is_positive(nb) || big_integer_is_zero(nb)) pc += *pc; else pc++;    break;
        }
        case BGLOAD: *sp++ = globals[*pc++];             break;
        case BGSTORE: globals[*pc++] = *--sp;            break;
        case BGPOP : {
            big_integer_free((big_integer *) sp);
            --sp;
            break;
        }
        case BGPUSH : {
            // Push a pointer to a big_integer to the top of the stack

            code read;
            cell *prev = NULL;
            cell *first = NULL;
            big_integer *nb = malloc(sizeof(big_integer));
            if (nb == NULL) {
                //TODO better error handling : Not enough memory
                syntax_error();
            }
            nb->count = 1;
            nb->sign = *pc++;
            nb->digits = NULL;
            read = *pc++;

            while (read != BIG_INTEGER_LIMITER) {

                // Add node to the big_integer
                cell *cell = malloc(sizeof(cell));
                if (!cell) {
                    //TODO better error handling : Not enough memory
                    syntax_error();
                }
                cell->next = NULL;
                if (prev != NULL) {
                    prev->next = cell;
                } else {
                    // If it has no previous node, then it's the first one
                    first = cell;
                }
                cell->digit = read;
                prev = cell;
                read = *pc++;
            }
            nb->digits = first;

            *sp++ = (long) nb;       // Add the pointer to the big_integer to the top of the stack.

            break;
        }
        case BGADD : {
            big_integer *a = (big_integer *) sp[-2], *b = (big_integer *) sp[-1];
            big_integer *c = big_integer_sum(a,b);
            sp[-2] = (long) c;
            sp--;
            //TODO free a and b
            break;
        }
        case BGSUB : {
            big_integer *a = (big_integer *) sp[-2], *b = (big_integer *) sp[-1];
            big_integer *c = big_integer_difference(a,b);
            sp[-2] = (long) c;
            sp--;
            //TODO free a and b
            break;
        }
        case BGDUP: {
            sp++; sp[-1] = sp[-2];
            // Add one to the number of counts of big_integer
            big_integer *bi = (big_integer *) sp[-1];
            bi->count += 1;
            break;
        }
          case BGMULT : {
              big_integer *a = (big_integer *) sp[-2], *b = (big_integer *) sp[-1];
              big_integer *c = big_integer_multiply(a,b);
              sp[-2] = (long) c;
              sp--;
              //TODO free a and b
              big_integer_free(a);
              big_integer_free(b);
              break;
          }
          case BGDIV  : {
              big_integer *a = (big_integer *) sp[-1];
              big_integer *c = big_integer_divide(a);
              sp[-1] = (long) c;
              sp--;

              //TODO free a and b
              big_integer_free(a);
              break;
          }
          case BGMOD  : {
              big_integer *a = (big_integer *) sp[-1];
              big_integer *c = big_integer_modulo(a);
              sp[-1] = (long) c;
              sp--;
              //TODO free a and b
              big_integer_free(a);
              break;
          }
        case RETURN: return;
    }
}

/*---------------------------------------------------------------------------*/

/* Programme principal. */

int main()
{

  freopen("code.c","r",stdin);
  int i;

  c(program());

#ifdef SHOW_CODE
  printf("\n");
#endif

  for (i=0; i<26; i++)
    globals[i] = 0;

    int j;
    for (j = 0; j < 1000; j++)
    {
        if (j > 0) printf(":");
        printf("%02d", object[j]);
    }
    printf("\n");

  run();

  for (i=0; i<26; i++){
      if (globals[i] != 0) {
          printf("%c = ", 'a' + i);
          big_integer_print(globals[i]);
          printf("\n");
      }
  }


  return 0;
}

/*---------------------------------------------------------------------------*/

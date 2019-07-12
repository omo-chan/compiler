#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <regex.h>

struct AST {
    char        *ast_type;   // 生成規則を区別
    struct AST	*parent;     // 親へのバックポインタ
    int	       	nth;         // 自分が何番目の兄弟か
    int         num_child;   // 子ノードの数
    struct AST  **child;     // 子ノードポインタの配列
    char        *lexeme;     // 葉ノード用 (整数，文字，文字列の定数，識別子）
};

/* ------------------------------------------------------- */
static void print_nspace (int n);
static struct AST* create_AST (char *ast_type, int num_child, ...);
static struct AST* create_leaf (char *ast_type, char *lexeme);
static struct AST* add_AST (struct AST *ast, int num_child, ...);
static void show_AST (struct AST *ast, int depth);
static void unparse_AST (struct AST *ast, int depth);

static struct AST* parse_translation_unit (void);

static char* map_file (char *filename);
static void my_regcomp (regex_t *regex_p, char *pattern);
static int my_regexec (regex_t *regex_p, char *str, regmatch_t *regmatch_p);
static void* copy_string_region_int (char *s, int start, int end);
static void* copy_string_region_ptr (char *start, char *end);
static void* copy_string_region_regmatch (char *s, regmatch_t *regmatch_p);
static int skip_block_comment (char *ptr, int off);
static int skip_whitespaces (char *ptr, int off);
static int strncmp_r (char *s1, char *s2);
static int check_kind_id (char *lexeme);
static int set_token_int (char *ptr, int begin, int end, int kind, int off);
static int set_token_regmatch (char *ptr, regmatch_t *regmatch_p, int kind, int off);
static void create_tokens (char *ptr);
static void dump_tokens ();
static struct AST* parse_exp(void);
static struct AST* parse_compound_statement ();
/* ------------------------------------------------------- */
// データ構造と変数

#define MAX_TOKENS 10000
struct token {
    int kind;
    int offset_begin;
    int offset_end;
    char *lexeme;
};
enum token_kind {
    TK_UNUSED    = 0,
    TK_ID        = 1,
    TK_INT       = 2,
    TK_CHAR      = 3,
    TK_STRING    = 4,
    TK_KW_CHAR   = 5,  // char
    TK_KW_ELSE   = 6,  // else
    TK_KW_GOTO   = 7,  // goto
    TK_KW_IF     = 8,  // if
    TK_KW_INT    = 9,  // int
    TK_KW_RETURN = 10, // return
    TK_KW_VOID   = 11, // void
    TK_KW_WHILE  = 12, // while
    TK_OP_EQ     = 13, // ==
    TK_OP_AND    = 14, // &&
    TK_OP_OR     = 15, // ||
    TK_KW_LONG   = 16, // long
    TK_COMMENT   = 17,  // デバッグ用
    TK_WHITESPACE = 18, // デバッグ用
    // 以下は名前を付けずにそのまま使う
    // ';' ':' '{' '}' ',' '=' '(' ')' '&' '!' '-' '+' '*' '/' '<'
};

char *token_kind_string[] = {
    "UNUSED", "ID", "INT", "CHAR", "STRING",
    "char", "else", "goto", "if", "int",
    "return", "void", "while", "==", "&&", "||", "long",
    [';'] = ";", [':'] = ":", ['{'] = "{", ['}'] = "}", [','] = ",",
    ['='] = "=", ['('] = "(", [')'] = ")", ['&'] = "&", ['!'] = "!",
    ['-'] = "-", ['+'] = "+", ['*'] = "*", ['/'] = "/", ['<'] = "<",
};

static struct token tokens [MAX_TOKENS];
static int tokens_index = 0;
static struct token *token_p; // for parsing

/* ------------------------------------------------------- */
static void
print_nspace (int n)
{
    printf ("%*s", n, "");
}

static void
printf_ns (int n, const char *format, ...)
{
    va_list arg;
    print_nspace (n*4); // 空文字列をn*4幅で印字
    va_start (arg, format);
    vprintf (format, arg);
    va_end (arg);
}

static struct AST*
create_AST (char *ast_type, int num_child, ...)
{
    va_list ap;
    struct AST *ast;
    ast = malloc (sizeof (struct AST));
    ast->parent = NULL;
    ast->nth    = -1;
    ast->ast_type = ast_type;
    ast->num_child = num_child;
    ast->lexeme = NULL;
    va_start (ap, num_child);
    if (num_child == 0) {
        ast->child = NULL;
    } else {
        int i;
    	ast->child = malloc (sizeof(struct AST *) * num_child);
	for (i = 0; i < num_child; i++) {
	    struct AST *child = va_arg (ap, struct AST *);
	    ast->child [i] = child;
	    if (child != NULL) {
		child->parent = ast;
		child->nth    = i;
	    }
    	}
    }
    va_end (ap);
    return ast;
}

static struct AST*
create_leaf (char *ast_type, char *lexeme)
{
    struct AST *ast;
    ast = malloc (sizeof (struct AST));
    ast->parent    = NULL;
    ast->nth       = -1;
    ast->ast_type  = ast_type;
    ast->num_child = 0;
    ast->child     = NULL;
    ast->lexeme    = lexeme;
    return ast;
}

static struct AST*
add_AST (struct AST *ast, int num_child, ...)
{
    va_list ap;
    int i, start = ast->num_child;
    ast->num_child += num_child;
    assert (num_child > 0);
    ast->child = realloc (ast->child, sizeof(struct AST *) * ast->num_child);
    va_start (ap, num_child);
    for (i = start; i < ast->num_child; i++) {
        struct AST *child = va_arg (ap, struct AST *);
        ast->child [i] = child;
        if (child != NULL) {
            child->parent = ast;
            child->nth    = i;
        }
    }
    va_end (ap);
    return ast;
}

static void
show_AST (struct AST *ast, int depth)
{
    int i;
    print_nspace (depth);
    if (   !strcmp (ast->ast_type, "TK_ID")
        || !strcmp (ast->ast_type, "TK_INT")
        || !strcmp (ast->ast_type, "TK_CHAR")
        || !strcmp (ast->ast_type, "TK_STRING")) {
        printf ("%s (%s)\n", ast->ast_type, ast->lexeme);
    } else {
        printf ("%s\n", ast->ast_type);
    }

    for (i = 0; i < ast->num_child; i++) {
        if (ast->child [i] != NULL) {
            show_AST (ast->child [i], depth +1);
        }
    }
}
/* ------------------------------------------------------- */
// 構文解析

static void
parse_error (void)
{
    fprintf (stderr, "parse error (%d-%d): %s (%s)\n",
             token_p->offset_begin, token_p->offset_end,
             token_kind_string [token_p->kind], token_p->lexeme);
    exit (1);
}

static int
lookahead (int i)
{
    return tokens [tokens_index + i - 1].kind;
}

static struct token*
next_token (void)
{
    token_p = &tokens [++tokens_index];
    assert (tokens_index < MAX_TOKENS);
    return token_p;
}

static struct token*
reset_tokens (void)
{
    tokens_index = 0;
    token_p = &tokens [tokens_index];
    return token_p;
}

static void
consume_token (enum token_kind kind)
{
    if (lookahead (1) == kind) {
        next_token ();
    } else {
        //printf("cousume_error\n");
        parse_error ();
    }
}
//***********************************************************************
static struct AST* parse_type_specifier(void){
  struct AST *ast;
  switch (lookahead (1)) {
    case TK_KW_INT:ast = create_AST("type_specifier_INT",0);break;
    case TK_KW_CHAR:ast = create_AST("type_specifier_CHAR",0);break;
    case TK_KW_VOID:ast = create_AST("type_specifier_VOID",0);break;
    case TK_KW_LONG:ast = create_AST("type_specifier_LONG",0);break;
    default:parse_error();break;
  }
  next_token ();
  return ast;
}

static struct AST* parse_declarator(void){
  struct AST *ast;
  next_token ();
  switch(lookahead(1)){
    case '(':
      ast = create_leaf("Leaf",strcat(tokens[tokens_index-1].lexeme,"()"));
      consume_token('(');
      consume_token(')');
      break;
    default:ast = create_leaf("Leaf",tokens[tokens_index-1].lexeme);break;
  }
  return ast;
}

static struct AST* parse_primary(void){
  struct AST *ast, *ast1,*ast05,*ast15;
  ast = create_AST ("parse_primary",0);
  switch (lookahead(1)) {
    case TK_INT: case TK_CHAR: case TK_STRING: case TK_ID:
    if (lookahead(0)=='(') {
      ast05 = create_leaf("Leaf","(");
      ast15 = create_leaf("Leaf",")");
      ast1 = create_leaf("Leaf",tokens[tokens_index].lexeme);
      ast = add_AST(ast,3,ast05,ast1,ast15);
    }else{
      ast1 = create_leaf("Leaf",tokens[tokens_index].lexeme);
      ast = add_AST(ast,1,ast1);
    }
    next_token();
    break;
    case '(':
    consume_token('(');
    ast1 = parse_exp();
    consume_token(')');
    ast = add_AST(ast,1,ast1);
    break;
    default:parse_error();
  }

  return ast;
}

static struct AST* parse_exp(void){
  struct AST *ast, *ast1, *ast2;
  ast = create_AST ("parse_exp", 0);
  ast1 = parse_primary();//lookahead(1)はINT,CHAR,STRING,ID,'(' '('の場合はconsumetoken必要

  if (lookahead(1)=='(') {
    consume_token('(');
    consume_token(')');
    ast2 = create_AST("()",0);
    ast = add_AST(ast,2,ast1,ast2);
  }else{
    ast = add_AST(ast,1,ast1);
  }
  return ast;
}

static struct AST* parse_statement(void){
  struct AST *ast, *ast1, *ast2, *ast3, *ast4, *ast5;
  ast = create_AST ("parse_statement", 0);
  switch (lookahead(1)) {
    case TK_ID://先読み必要
      if (lookahead(2) == ':') {//IDENTIFIER ":"の場合
        ast1 = create_leaf("Leaf_label",strcat(tokens[tokens_index].lexeme,":\n"));
        next_token();
        consume_token(':');
        ast = add_AST(ast,1,ast1);
        break;
      }else if (lookahead(2) == ';'||lookahead(2) == '(') {//expの時
        ast1 = parse_exp();//next_token含む
        consume_token (';');
        ast2 = create_AST (";", 0);
        ast = add_AST(ast,2,ast1,ast2);
        break;
      }
    case '{'://compound_statement
      ast1 = parse_compound_statement();
      ast = add_AST(ast,1,ast1);
      break;
    case TK_KW_IF:
      ast1 = create_AST("if",0);
      next_token();
      consume_token('(');
      ast2 = parse_exp();
      consume_token(')');
      ast3 = parse_statement();
      if (lookahead(1) == TK_KW_ELSE) {//if else文
        next_token();
        ast4 = create_AST("else",0);
        ast5 = parse_statement();
        ast = add_AST(ast,5,ast1,ast2,ast3,ast4,ast5);
      }else{
        ast = add_AST(ast,3,ast1,ast2,ast3);
      }
      break;
    case TK_KW_WHILE:
      ast1 = create_AST("while",0);
      next_token();
      consume_token('(');
      ast2 = parse_exp();
      consume_token(')');
      ast3 = parse_statement();
      ast = add_AST(ast,3,ast1,ast2,ast3);
      break;
    case TK_KW_GOTO:
      ast1 = create_AST("goto",0);
      next_token();
      ast2 = create_leaf("Leaf",tokens[tokens_index].lexeme);
      next_token();
      consume_token(';');
      ast3 = create_AST(";",0);
      ast = add_AST(ast,3,ast1,ast2,ast3);
      break;
    case TK_KW_RETURN:
      ast1 = create_AST("return",0);
      next_token();
      if (lookahead(1)==TK_INT ||lookahead(1)==TK_CHAR ||lookahead(1)==TK_STRING ||lookahead(1)==TK_ID ||lookahead(1)=='(') {
        //expの場合
        ast2 = parse_exp();
        ast3 = create_AST(";",0);
        ast = add_AST(ast,3,ast1,ast2,ast3);
        consume_token(';');
      }else if(lookahead(1)==';'){
        consume_token(';');
        ast2 = create_AST(";",0);
        ast = add_AST(ast,2,ast1,ast2);
      }
      break;
    case ';': //[exp];のexpなし
      ast1 = create_AST(";",0);
      ast = add_AST(ast,1,ast1);
      consume_token(';');
      break;
    case TK_INT: case TK_CHAR: case TK_STRING: case '(':
      ast1 = parse_exp();//ToDoここの問題解決
      consume_token (';');
      ast2 = create_AST (";", 0);
      ast = add_AST(ast,2,ast1,ast2);
      break;
    default:
      parse_error ();
      break;
  }
  return ast;
}

static struct AST* parse_compound_statement(void){
  struct AST *ast, *ast1, *ast2, *ast3;
  consume_token('{');
  ast = create_AST ("compound_statement", 0);
  while(1){
    switch(lookahead(1)){
    case TK_KW_INT: case TK_KW_CHAR: case TK_KW_VOID: case TK_KW_LONG:
          ast1 = parse_type_specifier ();//next_token含む
          ast2 = parse_declarator ();//next_token含む
          consume_token (';');
          ast3 = create_AST (";", 0);
          ast = add_AST (ast, 3, ast1, ast2, ast3);
          break;
    case '}':
          consume_token('}');
          goto loop_exit2;
          break;
    //case :"statement"
    case '{': case TK_KW_IF: case TK_KW_WHILE: case TK_KW_GOTO: case TK_KW_RETURN:
    case ';': case TK_ID: case TK_INT: case TK_CHAR: case TK_STRING: case '(':
          ast1 = parse_statement();//next_tokenを入れろ
          ast = add_AST (ast, 1, ast1);
          break;
    default:
          goto loop_exit2;
    }
  }
  loop_exit2:
      return ast;
}
//***********************************************************************
// translation_unit: ( type_specifier declarator ( ";" | compound_statement ))*
static struct AST*
parse_translation_unit (void)
{
    struct AST *ast, *ast1, *ast2, *ast3;

    ast = create_AST ("translation_unit", 0);
    while (1) {
        switch (lookahead (1)) {
        case TK_KW_INT: case TK_KW_CHAR: case TK_KW_VOID: case TK_KW_LONG://longを追加したほうがいい
            // parse_type_specifier などのコードを書く
              ast1 = parse_type_specifier ();
              ast2 = parse_declarator ();
            switch (lookahead (1)) {
            case ';':
                consume_token (';');
                ast3 = create_AST (";", 0);
                break;
            case '{':
                ast3 = parse_compound_statement ();
                break;
            default:
                parse_error ();
                break;
            }
              ast = add_AST (ast, 3, ast1, ast2, ast3);
            break;
        default:
            goto loop_exit;
        }
    }
loop_exit:
    return ast;
}

/* ------------------------------------------------------- */
// 字句解析

static char*
map_file (char *filename)
{
    struct stat sbuf;
    char *ptr;

    int fd = open (filename, O_RDWR);
    if (fd == -1) {
        perror ("open");
        exit (1);
    }

    fstat (fd, &sbuf);
#if 0
    printf ("file size = %lld\n", sbuf.st_size);
#endif

    ptr = mmap (NULL, sbuf.st_size + 1, // +1 for '\0'
                PROT_READ|PROT_WRITE, MAP_PRIVATE, fd, 0);
    if (ptr == MAP_FAILED) {
        perror ("mmap");
        exit (1);
    }
    ptr [sbuf.st_size] = '\0';
    return ptr;
}

static void
my_regcomp (regex_t *regex_p, char *pattern)
{
    static char buf [BUFSIZ];
    int ret = regcomp (regex_p, pattern, REG_EXTENDED);

    if (ret != 0) {
	regerror (ret, regex_p, buf, sizeof (buf));
	fprintf (stderr, "regcomp: %s\n", buf);
	exit (1);
    }
}

static int
my_regexec (regex_t *regex_p, char *str, regmatch_t *regmatch_p)
{
    int ret = regexec (regex_p, str, 1, regmatch_p, 0);
#if 0
    if (ret == 0) {
        fprintf (stderr, "matched: |%lld, %lld: %.40s|\n",
                 regmatch_p->rm_so, regmatch_p->rm_eo, str+regmatch_p->rm_so);
    } else {
        fprintf (stderr, "unmatched\n");
    }
#endif
    return ret;
}

static void*
copy_string_region_int (char *s, int start, int end)
{
    int size = end - start;
    char *buf = malloc (size + 1); // +1 for '\0'
    memcpy (buf, s+start, size);
    buf [size] = '\0';
    return buf;
}

static void*
copy_string_region_ptr (char *start, char *end)
{
    int size = end - start;
    char *buf = malloc (size + 1); // +1 for '\0'
    memcpy (buf, start, size);
    buf [size] = '\0';
    return buf;
}

static void*
copy_string_region_regmatch (char *s, regmatch_t *regmatch_p)
{
    return copy_string_region_int (s, regmatch_p->rm_so, regmatch_p->rm_eo);
}

static int skip_block_comment (char *ptr, int off)
{
    int i = off;

    assert ((ptr [i] == '/') && (ptr [i+1] == '*'));
    i += 2;
    while ((ptr [i] != '\0') && !(ptr [i] == '*' && ptr [i+1] == '/')) {
        i++;
    }
    if (ptr [i] != '\0')
        i += 2;

#if 0
    char *buf = copy_string_region_ptr (ptr + off, ptr + i);
    printf ("block_comment(%d-%d)=|%s|\n", off, i, buf);
    set_token_int (ptr, 0, i - off, TK_COMMENT, off);
#endif
    return i;
}

static int skip_whitespaces (char *ptr, int off)
{
    int i = off;

    while (ptr [i] != '\0') {
        int c = ptr [i];
        if (c == ' ' || c == '\t' || c == '\n') {
            i++;
        } else {
            break;
        }
    }
#if 0
    char *buf = copy_string_region_ptr (ptr + off, ptr + i);
    printf ("whitespaces(%d, %d)=|%s|\n", off, i, buf);
    set_token_int (ptr, 0, i - off, TK_WHITESPACE, off);
#endif
    return i;
}

static int
strncmp_r (char *s1, char *s2)
{
    return strncmp (s1, s2, strlen (s2));
}

static int
check_kind_id (char *lexeme)
{
    if      (!strcmp (lexeme, "char"))   return TK_KW_CHAR;
    else if (!strcmp (lexeme, "else"))   return TK_KW_ELSE;
    else if (!strcmp (lexeme, "goto"))   return TK_KW_GOTO;
    else if (!strcmp (lexeme, "if"))     return TK_KW_IF;
    else if (!strcmp (lexeme, "int"))    return TK_KW_INT;
    else if (!strcmp (lexeme, "long"))   return TK_KW_LONG;
    else if (!strcmp (lexeme, "return")) return TK_KW_RETURN;
    else if (!strcmp (lexeme, "void"))   return TK_KW_VOID;
    else if (!strcmp (lexeme, "while"))  return TK_KW_WHILE;
    else                                 return TK_ID;
}

static int
set_token_int (char *ptr, int begin, int end, int kind, int off)
{
    assert (tokens_index < MAX_TOKENS);
    struct token *token_p = &tokens [tokens_index++];
    assert (begin == 0);
    token_p->kind = kind;
    token_p->offset_begin = off + begin;
    token_p->offset_end   = off + end;
    token_p->lexeme = copy_string_region_int (ptr + off, begin, end);
#if 0
    printf ("topen_p->lexeme = |%s|\n", token_p->lexeme);
#endif
    return off + end;
}

static int
set_token_regmatch (char *ptr, regmatch_t *regmatch_p, int kind, int off)
{
    return set_token_int (ptr, regmatch_p->rm_so, regmatch_p->rm_eo, kind, off);
}

static void create_tokens (char *ptr)
{
    static char str_id     [] = "^[a-zA-Z_][a-zA-Z0-9_]*";
    static char str_int    [] = "^(0|[1-9][0-9]*)";
    // regcomp に渡すパターンは ^'(\\n|\\'|\\\\|[^\'])' エスケープすると以下
    static char str_char   [] = "^'(\\\\n|\\\\'|\\\\\\\\|[^\\'])'";
    // regcomp に渡すパターンは ^"(\\n|\\"|\\\\|[^\"])*" エスケープすると以下
    static char str_string [] = "^\"(\\\\n|\\\\\"|\\\\\\\\|[^\\\"])*\"";
    static regex_t regex_id, regex_int, regex_char, regex_string;
    static regmatch_t regmatch;

    char *ptr_start = ptr;
    int off = 0;

    my_regcomp (&regex_id,     str_id);
    my_regcomp (&regex_int,    str_int);
    my_regcomp (&regex_char,   str_char);
    my_regcomp (&regex_string, str_string);

    while (ptr [off] != '\0') {
        int ret;

        if ((ptr [off] == '/') && (ptr [off+1] == '*')) {
            off = skip_block_comment (ptr, off);
            continue;
        } else if (ptr [off] == ' ' || ptr [off] == '\t' || ptr [off] == '\n') {
            off = skip_whitespaces (ptr, off);
            continue;
        }

        ret = my_regexec (&regex_id, ptr + off, &regmatch);
        if (ret == 0) {
            char *lexeme = copy_string_region_regmatch (ptr + off, &regmatch);
            int kind = check_kind_id (lexeme);
            off = set_token_regmatch (ptr, &regmatch, kind, off);
            free (lexeme);
            continue;
        }
        ret = my_regexec (&regex_int, ptr + off, &regmatch);
        if (ret == 0) {
            off = set_token_regmatch (ptr, &regmatch, TK_INT, off);
            continue;
        }
        ret = my_regexec (&regex_char, ptr + off, &regmatch);
        if (ret == 0) {
            off = set_token_regmatch (ptr, &regmatch, TK_CHAR, off);
            continue;
        }
        ret = my_regexec (&regex_string, ptr + off, &regmatch);
        if (ret == 0) {
            off = set_token_regmatch (ptr, &regmatch, TK_STRING, off);
            continue;
        }

        {
            if      (!strncmp_r (ptr + off, "=="))
                off = set_token_int (ptr, 0, 2, TK_OP_EQ, off);
            else if (!strncmp_r (ptr + off, "&&"))
                off = set_token_int (ptr, 0, 2, TK_OP_AND, off);
            else if (!strncmp_r (ptr + off, "||"))
                off = set_token_int (ptr, 0, 2, TK_OP_OR, off);
            else {
                switch (ptr [off]) {
                case ';': off = set_token_int (ptr, 0, 1, ';', off); break;
                case ':': off = set_token_int (ptr, 0, 1, ':', off); break;
                case '{': off = set_token_int (ptr, 0, 1, '{', off); break;
                case '}': off = set_token_int (ptr, 0, 1, '}', off); break;
                case ',': off = set_token_int (ptr, 0, 1, ',', off); break;
                case '=': off = set_token_int (ptr, 0, 1, '=', off); break;
                case '(': off = set_token_int (ptr, 0, 1, '(', off); break;
                case ')': off = set_token_int (ptr, 0, 1, ')', off); break;
                case '&': off = set_token_int (ptr, 0, 1, '&', off); break;
                case '!': off = set_token_int (ptr, 0, 1, '!', off); break;
                case '-': off = set_token_int (ptr, 0, 1, '-', off); break;
                case '+': off = set_token_int (ptr, 0, 1, '+', off); break;
                case '*': off = set_token_int (ptr, 0, 1, '*', off); break;
                case '/': off = set_token_int (ptr, 0, 1, '/', off); break;
                case '<': off = set_token_int (ptr, 0, 1, '<', off); break;
                default:
                    printf ("unexpected token (%d): %s\n", off, ptr + off);
                    exit (1);
                }
            }
        }
    }
}

static void dump_tokens ()
{
    int i;
    for (i = 0; i < MAX_TOKENS; i++) {
        struct token *token_p = &tokens [i];
        if (token_p->kind == TK_UNUSED)
            break;
        printf ("%5d: %d-%d: %s (%s)\n", i,
                token_p->offset_begin,
                token_p->offset_end,
                token_p->lexeme,
                token_kind_string [token_p->kind]);
    }
}
/* ------------------------------------------------------- */
static void
unparse_error (struct AST *ast)
{
    printf ("something wrong: %s\n", ast->ast_type);
    exit (1);
}

static void
unparse_AST (struct AST *ast, int depth)
{
    int i;
    if (!strcmp (ast->ast_type, "translation_unit")) {
        for (i = 0; i < ast->num_child; i++) {
            printf_ns (depth, "");
            unparse_AST (ast->child [i],   depth+1);
            unparse_AST (ast->child [i+1], depth+1);
            if (!strcmp (ast->child [i+2]->ast_type, ";")) {
                printf (";\n");
            } else if (!strcmp (ast->child [i+2]->ast_type,
                                "compound_statement")) {
                unparse_AST (ast->child [i+2], depth+1);
            } else {
                unparse_error (ast);
            }
            i+=2;
        }
/*
  ここにコードを書く************************************************************
 */
    }else if(!strcmp (ast->ast_type, "type_specifier_INT")){
        printf("int ");
    }else if(!strcmp (ast->ast_type, "type_specifier_VOID")){
        printf("void ");
    }else if(!strcmp (ast->ast_type, "type_specifier_CHAR")){
        printf("char ");
    }else if(!strcmp (ast->ast_type, "type_specifier_LONG")){
        printf("long ");
    }else if(!strcmp (ast->ast_type, "if")){
        printf("if");
    }else if(!strcmp (ast->ast_type, "else")){
        printf_ns(depth-1,"");
        printf("else ");
    }else if(!strcmp (ast->ast_type, "while")){
        printf("while");
    }else if(!strcmp (ast->ast_type, "goto")){
        printf("goto ");
    }else if(!strcmp (ast->ast_type, "return")){
        printf("return ");
    }else if(!strcmp (ast->ast_type, ";")){
        printf(";\n");
    }else if(!strcmp (ast->ast_type, "()")){
        printf("()");
    }else if(!strcmp (ast->ast_type, "parse_primary")){
        for (i = 0; i < ast->num_child; i++) {
          unparse_AST(ast->child [i],   depth);
        }
    }else if(!strcmp (ast->ast_type, "parse_exp")){
      for (i = 0; i < ast->num_child; i++) {
        unparse_AST(ast->child [i],   depth);
      }
    }else if(!strcmp (ast->ast_type, "parse_statement")){
      if ((!strcmp(ast->child [0]->ast_type,"if"))&&(strcmp(ast->child [2]->child[0]->ast_type,"compound_statement")!=0)) {
        //ifのあとに{}がない場合
        unparse_AST(ast->child [0],   depth);
        unparse_AST(ast->child [1],   depth);
        printf("\n");
        printf_ns(depth-1,"");
        printf("{\n");
        printf_ns(depth,"");
        unparse_AST(ast->child [2],   depth+1);
        printf_ns(depth-1,"");
        printf("}\n");
        if (ast->num_child == 5) {//elseありの時でelseの後にも{}がないとき
          if (strcmp(ast->child [4]->child[0]->ast_type,"compound_statement")!=0) {
            unparse_AST(ast->child [3],   depth);
            printf("\n");
            printf_ns(depth-1,"");
            printf("{\n");
            printf_ns(depth,"");
            unparse_AST(ast->child [4],   depth+1);
            printf_ns(depth-1,"");
            printf("}\n");
          }else{//elseの後には{}がある場合
            unparse_AST(ast->child [3],   depth);
            unparse_AST(ast->child [4],   depth);
          }
        }
      }else{
        for (i = 0; i < ast->num_child; i++) {
          unparse_AST(ast->child [i],   depth);
        }
      }

    }else if(!strcmp (ast->ast_type, "compound_statement")){
        printf("\n");
        printf_ns(depth-1,"");
        printf("{\n");//type_specifierとstatementを分けて処理したほうがいいかも
        for (i = 0; i < ast->num_child; i++) {
          if (!strcmp(ast->child[i]->ast_type,"parse_statement")) {
            if (!strcmp(ast->child[i]->child[0]->ast_type,"Leaf_label")) {
            }else{
              printf_ns(depth,"");
            }
            unparse_AST(ast->child [i],   depth+1);
          }else{
            printf_ns(depth,"");
            unparse_AST(ast->child [i],   depth+1);
            unparse_AST(ast->child [i+1],   depth+1);
            if (!strcmp (ast->child [i+2]->ast_type, ";")) {
                printf (";\n");
            }
            i+=2;
          }
        }
        printf_ns(depth-1,"");
        printf("}\n");
    }else if(!strcmp (ast->ast_type, "Leaf")){
      printf("%s",ast->lexeme);
    }else if(!strcmp (ast->ast_type, "Leaf_label")){
      printf("%s",ast->lexeme);
    }
//***************************************************************************
    else {
        unparse_error (ast);
    }
}
/* ------------------------------------------------------- */

int main (int argc, char *argv[])
{
    char *ptr;
    struct AST *ast;

    if (argc != 2) {
        fprintf (stderr, "Usage: %s filename\n", argv[0]);
        exit (1);
    }

    ptr = map_file (argv [1]);
    create_tokens (ptr);
    reset_tokens ();
     //dump_tokens ();    // 提出時はコメントアウトしておくこと
    ast = parse_translation_unit ();
     //show_AST (ast, 0); // 提出時はコメントアウトしておくこと
    unparse_AST (ast, 0);
}

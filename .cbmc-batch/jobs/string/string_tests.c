#include <aws/common/string.h>
#include <stddef.h>

const size_t MAX_STRING_LEN = 64;

void assert_bytes_match(const uint8_t* a, const uint8_t* b, size_t len)
{
  if (len > 0){
    size_t i;
    __CPROVER_assume(i < len);
    assert(a[i] == b[i]);
  }
}

void assert_all_bytes_are(const uint8_t* a, const uint8_t c, size_t len)
{
  if (len > 0){
    size_t i;
    __CPROVER_assume(i < len);
    assert(a[i] == c);
  }
}

void assert_all_zeroes(const uint8_t* a, size_t len)
{
  assert_all_bytes_are(a, 0, len);
}

void aws_string_bytes_harness()
{
  size_t len;
  struct aws_string* str = make_arbitrary_aws_string(can_fail_allocator(), len);
  aws_string_bytes(str);
}

void aws_string_eq_harness()
{
  struct aws_string* str_a = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);
  struct aws_string* str_b = nondet_bool()
    ? str_a : make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);;
  aws_string_eq(str_a, str_b);
}

//byte cursor
//byte buffer

void aws_string_new_from_c_str_harness() {
  size_t alloc_len;
  __CPROVER_assume(alloc_len <= MAX_STRING_LEN);
  size_t max_strlen;
  __CPROVER_assume(max_strlen < alloc_len);

  
  uint8_t* c_str = malloc(alloc_len);
  c_str[max_strlen] = '\0';//Ensure that the string is no longer than max_strlen.
  //Note that strlen may be shorter than max_strlen if the string has another null character in it
  struct aws_string* aws_str = aws_string_new_from_c_str(can_fail_allocator(), c_str);
  assert(aws_str->len == strlen(c_str));
  assert(aws_str->bytes[aws_str->len] == '\0');
  assert_bytes_match(aws_str->bytes, c_str, aws_str->len);
}

void aws_string_new_from_array_harness()
{
  size_t alloc_len;
  __CPROVER_assume(alloc_len <= MAX_STRING_LEN);
  uint8_t* array = malloc(alloc_len);
  size_t reported_size;
  __CPROVER_assume(reported_size <= alloc_len);
  struct aws_string* aws_str = aws_string_new_from_array(can_fail_allocator(), array, reported_size);
  assert(aws_str->len == reported_size);
  assert(aws_str->bytes[aws_str->len] == '\0');
  assert_bytes_match(aws_str->bytes, array, aws_str->len);  
}

void aws_string_new_from_string_harness()
{

  struct aws_string* str_a = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);
  struct aws_string* str_b = aws_string_new_from_string(str_a->allocator, str_a);
  assert(str_a->len == str_b->len);
  assert(str_b->bytes[str_b->len] == '\0');
  assert_bytes_match(str_a->bytes, str_b->bytes, str_a->len);
}


void aws_string_destroy_harness(){
  struct aws_string* str =  make_arbitrary_aws_string_nondet_len(can_fail_allocator());
  aws_string_destroy(str);
}

void aws_string_destroy_secure_harness(){
  struct aws_string* str =  make_arbitrary_aws_string_nondet_len(can_fail_allocator());
  aws_string_destroy_secure(str);
  //TODO see if there is a way to check that the memory really was zeroed
}



void aws_string_compare_harness()
{
  struct aws_string* str_a = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);
  struct aws_string* str_b = nondet_bool()
    ? str_a : make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);;
  int rval = aws_string_compare(str_a, str_b);
  //TODO is there a clean CBMC check to do here?
}

void aws_array_list_comparator_string_harness()
{
  struct aws_string* str_a = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);
  struct aws_string* str_b = nondet_bool()
    ? str_a : make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);;
  int rval = aws_array_list_comparator_string(str_a, str_b);
  //TODO is there a clean CBMC check to do here?
}

void aws_byte_buf_write_from_whole_string_harness() {

}

void aws_byte_cursor_from_string_harness() {

}

# Usage
```
mkdir in out
mkdir in/config_queue in/input_queue
echo a=1 > in/config_queue/test
echo aaaaaa > in/input_queue/test
./afl-fuzz -i in -o out -d ./test out/.cur_config
```

# fuzzing with argv

1. Include "argv-fuzz-inl.h".
2. Put `AFL_INIT_ARGV()` at the beginning of `main` function.
3. Same as the usage above.
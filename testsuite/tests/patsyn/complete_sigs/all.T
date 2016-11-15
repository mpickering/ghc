test('simple', normal, compile, [''])
test('empty', normal, compile, [''])
test('Module', normal, multimod_compile, ['Module', '-Wall'])
test('ty-mismatch', normal, compile_fail, [''])


**탐험준비 - Week06 Malloc lab(말록랩)**

<aside>
💡 **지난 주에 사용했던 malloc을 이번 주에는 만들어 보아요**

</aside>

- '동적 메모리 할당' 방법을 직접 개발하면서 메모리, 포인터 개념에 익숙해질 수 있는 과제입니다. 랩 코드를 직접 수정하고, 채점 프로그램을 실행하면서 '내 점수'를 알 수 있습니다.
    
    → 즉, 나만의 malloc, realloc, free 함수를 구현하는 것!
    
- implicit, explicit, seglist 등 여러 방법이 있지만, 일단 `implicit` 방법부터 구현해 보겠습니다. 여유가 되면 explicit, seglist, buddy system 까지도 도전해보세요.
- 컴퓨터 시스템 교재의 9.9장을 찬찬히 읽어가며 진행하세요. 교재의 코드를 이해하고 옮겨써서 잘 동작하도록 실행해보는 것이 시작입니다!
- [https://github.com/SWJungle/malloclab-jungle](https://github.com/SWJungle/malloclab-jungle) 의 내용대로 진행합니다.
    - '컴퓨터 시스템'책의 `malloclab-handout`의 내용을 따라합니다.
    - `mm.c`를 구현하고 `mdriver`로 채점(테스트) 합니다.
    - 진행방법
        1. make 후 `./mdriver` 를 실행하면 `out of memory` 에러 발생
        2. 책에 있는 implicit list 방식대로 malloc을 구현해서 해당 에러를 없애기
        3. 이후 (시간이 된다면) explicit list와 seglist 등을 활용해 점수를 높이기
        
        - Tip: `./mdriver -f traces/binary2-bal.rep` 와 같이 특정 세트로만 채점 할 수 있다.
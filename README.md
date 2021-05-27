# par-uniq-id

제목: 고성능 병렬컴퓨팅을 위한 Lock-Free 고유 식별자 할당

## 서론
많은 시간이 걸리는 큰 작업을 여러 개의 작은 작업으로 분할할 수 있고
서로 의존성이 없다면 병렬처리를 통해 성능 향상을 기대할 수 있다.
그런데 핵심 알고리듬을 검토했을 때는 의존성이 없더라도
로그를 남기거나 트랙잭션 번호를 부여하는 등의 부가적 기능이
순차적 의존성이 있는 방식으로 구현되어 있는 경우가 많아
기대했던 만큼의 성능 향상이 이루어지지 못한다. 이런 부가적
기능에서 공통적으로 많이 필요한 요소가 고유 식별자 할당이다.
따라서 병렬 컴퓨팅의 적합한 방법으로 고유 식별자를 할당할
수 있다면 부가적인 기능에서 병목 없이 병렬화를 통해 성능을
원활하게 향상시킬 수 있을 것으로 기대된다.

분산 컴퓨팅에서도 비슷한 문제를 다양한 방법으로 해결하고 있다.
(예를 1-10000, 10001-20000, 20001-30000, ...)
이런 아이디어를 멀티코어 기반의 병렬 컴퓨팅에 적용하면 성능을 향상시킬 수 있음을 확인하였다 ....
...

## 본론
서론에서 언급한 특정 구간을 정해 고유 식별자를 할당하는 것도 좋은 방법이지만
필요한 고유 식별자의 개수를 미리 예상할 수 있어야 한다. 필요한 고유 식별자의
개수의 예상이 어렵거나 가능하더라도 그것을 파악하는 데 복잡한 계산이 필요한
경우에는 효과적이지 못한 방법이다. 우리는 각 병렬 작업에서 필요한 고유 식별자
개수를 신경쓰지 않고 Lock 없이 여러 병렬 작업에 고유 식별자를 할당하는 방법을
제안하고 구현하여 Lock을 활용한 방식과 성능을 비교하는 간단한 벤치마크를 수행하였다.

## 방법

k를 1씩 증가 그러니까 이번엔 k를 사용하고 다음번에는 (k+1,1) 이런 식으로 진행
(k,1)

이러다 3개로 나눠서 병렬로 돌리려면

(k,3), (k+1,3), (k+2,3) 으로 나눠서 진행

일반적으로 k를 i씩 증가 그러니까 이번엔 k를 사용하고 다음번엔 (k+i,i) 이런 식으로
(k,i)

이러다 n개로 나눠서 돌리면
`(k,i*n), (k+1,i*n), ..., (k+n-1,i*n)`

### 그림1. 1씩 증가하는 흐름을 3개의 작업으로 분기하여 병렬 실행 후 다시 합쳐 진행하는 `runParallel`의 동작 방식
[![](https://mermaid.ink/img/eyJjb2RlIjoic3RhdGVEaWFncmFtLXYyXG4gICAgXG5zdGF0ZSBmb3JrIDw8Zm9yaz4-XG5SOiDii65cXG4oay0yLCAxKVxcbihrLTEsIDEpXFxuKGsgLCAxKVxuUzA6IChrKzAsIDMpXFxuKGsrMywgMylcXG4g4ouuXFxuKHggLCAzKVxuUzE6IChrKzEsIDMpXFxuKGsrNCwgMylcXG7ii65cXG4oeSAsIDMpXG5TMjogKGsrMiwgMylcXG4oays1LCAzKVxcbuKLrlxcbih6ICwgMylcblQ6IChtYXgoeCx5LHopLCAxKVxcbihtYXgoeCx5LHopKzEsIDEpXFxuKG1heCh4LHkseikrMiwgMSlcXG7ii65cXG5cblxuUiAtLT4gZm9ya1xuZm9yayAtLT4gUzBcbmZvcmsgLS0-IFMxXG5mb3JrIC0tPiBTMlxuXG5zdGF0ZSBqb2luIDw8am9pbj4-XG5TMCAtLT4gam9pblxuUzEgLS0-IGpvaW5cblMyIC0tPiBqb2luXG5qb2luIC0tPiBUXG5cbiIsIm1lcm1haWQiOnsidGhlbWUiOiJkZWZhdWx0In0sInVwZGF0ZUVkaXRvciI6ZmFsc2V9)](https://mermaid-js.github.io/mermaid-live-editor/#/edit/eyJjb2RlIjoic3RhdGVEaWFncmFtLXYyXG4gICAgXG5zdGF0ZSBmb3JrIDw8Zm9yaz4-XG5SOiDii65cXG4oay0yLCAxKVxcbihrLTEsIDEpXFxuKGsgLCAxKVxuUzA6IChrKzAsIDMpXFxuKGsrMywgMylcXG4g4ouuXFxuKHggLCAzKVxuUzE6IChrKzEsIDMpXFxuKGsrNCwgMylcXG7ii65cXG4oeSAsIDMpXG5TMjogKGsrMiwgMylcXG4oays1LCAzKVxcbuKLrlxcbih6ICwgMylcblQ6IChtYXgoeCx5LHopLCAxKVxcbihtYXgoeCx5LHopKzEsIDEpXFxuKG1heCh4LHkseikrMiwgMSlcXG7ii65cXG5cblxuUiAtLT4gZm9ya1xuZm9yayAtLT4gUzBcbmZvcmsgLS0-IFMxXG5mb3JrIC0tPiBTMlxuXG5zdGF0ZSBqb2luIDw8am9pbj4-XG5TMCAtLT4gam9pblxuUzEgLS0-IGpvaW5cblMyIC0tPiBqb2luXG5qb2luIC0tPiBUXG5cbiIsIm1lcm1haWQiOnsidGhlbWUiOiJkZWZhdWx0In0sInVwZGF0ZUVkaXRvciI6ZmFsc2V9)

### 그림2. Lock-Free 고유 식별자 할당 라이브러리 기반 병렬화 벤치마크
이걸 실행한 걸 그래프 차트로 그림으로 만들어주세요. `-N`다음에 최대 병렬 스레드 활용 개수랑 실행 시간 비교 그래프로요 

Total time에 다음에 괄호 안에 있는 게 실제 걸린 시간입니다.

연구실 제 컴에서는 첫번째 줄 실행한 게 3~4초대 걸리고 조금씩 줄어들어서 2초대 정도로 가는데

돌리는 컴퓨터 상황에 따라서 2000000 대신에 개수는 조금 조정해도 되고요 한번 돌리는 데 너무 오래 걸리거나 그러면


```
stack run -- 1 8 2000000 +RTS -s -N1
stack run -- 1 8 2000000 +RTS -s -N2
stack run -- 1 8 2000000 +RTS -s -N3
stack run -- 1 8 2000000 +RTS -s -N4
stack run -- 1 8 2000000 +RTS -s -N5
stack run -- 1 8 2000000 +RTS -s -N6
stack run -- 1 8 2000000 +RTS -s -N7
stack run -- 1 8 2000000 +RTS -s -N8
```

### 그림3. Lock 활용 공유 메모리 기반 고유 식별자 항당 병렬화 벤치마크
마찬가지로 3번도 그래프 차트 만들어 주세요. 마찬가지로 컴퓨터 상황에 따라 100000 를 조금 조정해도 되고.

```
stack run -- 2 8 100000 +RTS -s -N1
stack run -- 2 8 100000 +RTS -s -N2
stack run -- 2 8 100000 +RTS -s -N3
stack run -- 2 8 100000 +RTS -s -N4
stack run -- 2 8 100000 +RTS -s -N5
stack run -- 2 8 100000 +RTS -s -N6
stack run -- 2 8 100000 +RTS -s -N7
stack run -- 2 8 100000 +RTS -s -N8
```

## 구현 및 벤치마크

## 결론
나머지 연산(modular arithmetic)을 활용한 고유 식별자를 할당 방식은 
다음과 같은 장점이 있어 다양한 방식의 병렬 프로그램에 적용할 수 있다.
(1) Lock이 필요하지 않고,
(2) 병렬 작업이 요구하는 식별자 개수를 미리 파악할 필요가 없으며,
(3) 분기된 병렬 작업 내에서 재분기하는 경우에도 유연하게 활용 가능하다.
벤치마크를 통해 Lock이 배제된 결정적 병렬화 방식으로 구성된 병렬
프로그램에 활용해도 성능에 방해가 되지 않는다는 것을 벤치마크로 확인하였다.
향후 연구로는 ...

## 참고문헌

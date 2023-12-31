export const GuidebookContent = `
<!DOCTYPE html>
<html>

<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>iProve Language Guidebook</title>
  <link rel="stylesheet" href="/guidebook-style.css" />
</head>

<body class="stackedit">
  <div class="stackedit__left">
    <div class="stackedit__toc">
      
<ul>
<li><a href="#iprove-language-guidebook">iProve Language Guidebook</a>
<ul>
<li><a href="#before-writing-proofs">Before writing proofs</a></li>
<li><a href="#writing-a-formula">Writing a formula</a></li>
<li><a href="#proof-tactics">Proof tactics</a>
<ul>
<li></li>
</ul>
</li>
<li><a href="#function-definitions">Function definitions</a></li>
<li><a href="#partial-functions">Partial functions</a></li>
<li><a href="#induction">Induction</a></li>
</ul>
</li>
</ul>

    </div>
  </div>
  <div class="stackedit__right">
    <div class="stackedit__html">
      <h1 id="iprove-language-guidebook">iProve Language Guidebook</h1>
<p>Think you understand the iProve UI, but want to get to grips with the language? This document is a ~10 minute read and covers all the features of the language.</p>
<blockquote>
<p>Keep it open in another tab to use as reference!</p>
</blockquote>
<h2 id="before-writing-proofs">Before writing proofs</h2>
<h3 id="types">Types</h3>
<p>As with any programming language, the first thing we need to do is tell iProve what our variables are called, and what their types are. iProve is based on a <strong>Many-Sorted Logic</strong>, which is different from a standard type system in one crucial way: <strong>every variable has exactly one sort (type)</strong> - i.e. there is no subtyping built in. Other than that, types look fairly familiar. We have some built-in primitive types which will be familiar:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">Int</span>
<span class="token constant">Bool</span>
<span class="token constant">Real</span>
</code></pre>
<p>We can also use parameterized types borrowing the same syntax as C++, with the following builtins (we’ll talk about how to create them and extract the values from them later!):</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">List</span><span class="token operator">&lt;</span><span class="token constant">T</span><span class="token operator">&gt;</span>
<span class="token constant">Pair</span><span class="token operator">&lt;</span><span class="token constant">A</span><span class="token punctuation">,</span><span class="token constant">B</span><span class="token operator">&gt;</span>
<span class="token constant">Tuple</span><span class="token operator">&lt;</span><span class="token constant">A</span><span class="token punctuation">,</span><span class="token constant">B</span><span class="token punctuation">,</span><span class="token constant">C</span><span class="token punctuation">,</span><span class="token constant">D</span><span class="token operator">&gt;</span>
</code></pre>
<p>We have the familiar synonyms for tuple and list types:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token punctuation">[</span><span class="token constant">T</span><span class="token punctuation">]</span>      <span class="token operator">&lt;-&gt;</span>     <span class="token constant">List</span><span class="token operator">&lt;</span><span class="token constant">T</span><span class="token operator">&gt;</span>
<span class="token punctuation">(</span><span class="token constant">A</span><span class="token punctuation">,</span><span class="token constant">B</span><span class="token punctuation">)</span>    <span class="token operator">&lt;-&gt;</span>     <span class="token constant">Tuple</span><span class="token operator">&lt;</span><span class="token constant">A</span><span class="token punctuation">,</span><span class="token constant">B</span><span class="token operator">&gt;</span>    <span class="token operator">&lt;-&gt;</span>    <span class="token constant">Pair</span><span class="token operator">&lt;</span><span class="token constant">A</span><span class="token punctuation">,</span><span class="token constant">B</span><span class="token operator">&gt;</span>
</code></pre>
<p>Note that there’s no shorthand for singleton tuples.</p>
<p>We can define inductive types using the same syntax as Haskell:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token keyword">data</span> <span class="token constant">List</span> <span class="token constant">T</span> <span class="token operator">=</span> <span class="token hvariable">nil</span> <span class="token operator">|</span> <span class="token constant">Cons</span> <span class="token constant">T</span> <span class="token constant">List</span><span class="token operator">&lt;</span><span class="token constant">T</span><span class="token operator">&gt;</span>
<span class="token keyword">data</span> <span class="token constant">Pair</span> <span class="token constant">T</span> <span class="token constant">S</span> <span class="token operator">=</span> <span class="token constant">Pair</span> <span class="token constant">T</span> <span class="token constant">S</span>
<span class="token keyword">data</span> <span class="token constant">Maybe</span> <span class="token constant">T</span> <span class="token operator">=</span> <span class="token constant">Nothing</span> <span class="token operator">|</span> <span class="token constant">Just</span> <span class="token constant">T</span>
</code></pre>
<p>We can also define uninterpreted types which have no builtin support, but can be used to create types for which it can be guaranteed that Z3’s underlying solver will know nothing about</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token keyword">type</span> <span class="token constant">MysteryType</span>
</code></pre>
<h3 id="declarations">Declarations</h3>
<p>Now we know what our types look like, we can declare variables!</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">var</span> <span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token keyword">type</span>
<span class="token builtin">const</span> <span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token keyword">type</span>
</code></pre>
<p>In iProve, we can use either <code>var</code> or <code>const</code> to begin our declarations, but each is a synonym for the other! In first-order logic <em>all</em> data is immutable, but it sometimes make more sense to use <code>var</code> to remind us as we’re writing the proof. Every variable <em>must</em> be declared with a sort.</p>
<p>Now we have data to mutate,we can define some ways to mutate it:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">f</span> <span class="token operator">::</span> <span class="token constant">A</span> <span class="token operator">-&gt;</span> <span class="token constant">B</span>                            <span class="token comment">--  f :: A -&gt; B</span>
<span class="token hvariable">g</span> <span class="token operator">::</span> <span class="token punctuation">(</span><span class="token constant">A</span><span class="token punctuation">,</span> <span class="token constant">B</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">C</span>                       <span class="token comment">--  g :: A -&gt; B -&gt; C</span>
<span class="token hvariable">h</span> <span class="token operator">::</span> <span class="token punctuation">(</span><span class="token punctuation">(</span><span class="token constant">A</span><span class="token punctuation">,</span> <span class="token constant">B</span><span class="token punctuation">)</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token punctuation">(</span><span class="token constant">A</span><span class="token punctuation">,</span><span class="token constant">B</span><span class="token punctuation">,</span><span class="token constant">C</span><span class="token punctuation">)</span>               <span class="token comment">--  h :: (A, B) -&gt; (A, B, C)</span>
</code></pre>
<p>Just like variables, we need to declare all functions before using them. Above are some examples of iProve function declaration syntax, with intuitive corresponding Haskell syntax commented. The above code declares:</p>
<ul>
<li>The function <code>f</code> accepting one parameter of type <code>A</code> and returning the single value <code>B</code></li>
<li>The function <code>g</code> accepting two parameters of type <code>A</code> adnd <code>B</code>, and returning the single value C</li>
<li>The function <code>h</code> accepting one parameter of type <code>Pair&lt;A,B&gt;</code> and returning the three values <code>A,B,C</code>as a single instance of <code>Tuple&lt;A,B,C&gt;</code></li>
</ul>
<p>An incredibly important distinction between Haskell and first-order logic is that functions are <strong>not first-class</strong> and therefore cannot be used as parameters in a function signature. As an immediate corollary, currying is impossible, and this is reflected in the syntax for a function which accepts two arguments.</p>
<p>We have some builtin function type templates and their corresponding meaning:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">P</span>    <span class="token operator">::</span> <span class="token constant">Predicate</span><span class="token operator">&lt;</span><span class="token constant">A</span><span class="token punctuation">,</span> <span class="token constant">B</span><span class="token operator">&gt;</span>      <span class="token comment">-- P   :: (A, B) -&gt; Bool         1+ parameters</span>
<span class="token constant">R</span>    <span class="token operator">::</span> <span class="token constant">Relation</span><span class="token operator">&lt;</span><span class="token constant">Int</span><span class="token operator">&gt;</span>        <span class="token comment">-- R   :: (Int, Int) -&gt; Bool     1 parameter</span>
<span class="token builtin">div</span>  <span class="token operator">::</span> <span class="token constant">Operation</span><span class="token operator">&lt;</span><span class="token constant">Real</span><span class="token operator">&gt;</span>      <span class="token comment">-- div :: (Int, Int) -&gt; Int      1 parameter</span>
<span class="token constant">S</span>    <span class="token operator">::</span> <span class="token constant">Set</span><span class="token operator">&lt;</span><span class="token constant">Int</span><span class="token operator">&gt;</span>             <span class="token comment">-- P   :: Int -&gt; Bool            1 parameters</span>
</code></pre>
<p>An immediate question is why sets are represented as functions, and this is due to the fact that in first-order logic, sets are also <strong>not first-class</strong>. Indeed, under ZFC sets and functions can be seen as equivalent - FOL, however, does not have the capacity to state ZFC. In logic, we often talk about predicates and sets as interchangeable, and this formalises that notion. In iProve, a “set” is just a predicate. An element is “in” the set if the predicate returns true, and “not in” it otherwise.</p>
<p>POP QUIZ: Why do we not have to worry about Russell’s paradox?</p>
<blockquote>
<p>Sets are just functions, and functions are not first-class. As a result, we cannot have a set of sets.</p>
</blockquote>
<h2 id="writing-a-formula">Writing a formula</h2>
<h3 id="overall-syntax">Overall syntax</h3>
<p>Formulae are written in the syntax of first-order logic. This can be described by:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">Term</span>          <span class="token operator">::=</span> <span class="token constant">Atom</span> <span class="token operator">|</span> <span class="token operator">&lt;</span><span class="token hvariable">operator</span><span class="token operator">&gt;</span> <span class="token constant">Term</span> <span class="token operator">|</span> <span class="token constant">Atom</span> <span class="token operator">&lt;</span><span class="token hvariable">operator</span><span class="token operator">&gt;</span> <span class="token constant">Term</span> <span class="token operator">|</span> <span class="token constant">QuantFormula</span>
<span class="token constant">QuantFormula</span>  <span class="token operator">::=</span> <span class="token punctuation">(</span><span class="token constant">FA</span><span class="token operator">|</span><span class="token constant">EX</span><span class="token punctuation">)</span>  <span class="token punctuation">(</span><span class="token operator">&lt;</span><span class="token hvariable">variable</span><span class="token operator">&gt;:&lt;</span><span class="token keyword">type</span><span class="token operator">&gt;</span><span class="token punctuation">,</span> <span class="token operator">....</span><span class="token punctuation">,</span> <span class="token operator">&lt;</span><span class="token hvariable">variable</span><span class="token operator">&gt;:&lt;</span><span class="token keyword">type</span><span class="token operator">&gt;</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token constant">Term</span><span class="token punctuation">]</span>
<span class="token constant">Atom</span>          <span class="token operator">::=</span> <span class="token operator">&lt;</span><span class="token hvariable">function</span><span class="token operator">&gt;</span><span class="token punctuation">(</span><span class="token constant">Term</span><span class="token punctuation">,</span><span class="token operator">...</span><span class="token punctuation">,</span><span class="token constant">Term</span><span class="token punctuation">)</span> <span class="token operator">|</span> <span class="token operator">&lt;</span><span class="token hvariable">variable</span><span class="token operator">&gt;</span> <span class="token operator">|</span> <span class="token operator">&lt;</span><span class="token hvariable">literal</span><span class="token operator">&gt;</span> <span class="token operator">|</span> <span class="token constant">ParenTerm</span>
<span class="token constant">ParenTerm</span>     <span class="token operator">::=</span> <span class="token punctuation">[</span> <span class="token constant">Term</span> <span class="token punctuation">]</span> <span class="token operator">|</span> <span class="token punctuation">(</span> <span class="token constant">Term</span> <span class="token punctuation">)</span>
</code></pre>
<p>Variable/Function/type names can consist of any combination of the characters:</p>
<pre><code>abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVQXYZ0123456789_
</code></pre>
<p>Number literals can be in integer or decimal format.</p>
<p>We have some builtin operators provided which perform as expected</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token operator">+</span><span class="token punctuation">,</span> <span class="token operator">-</span><span class="token punctuation">,</span> <span class="token operator">*</span><span class="token punctuation">,</span> <span class="token operator">/</span><span class="token punctuation">,</span>       <span class="token comment">-- (&lt;numeric type&gt;, &lt;numeric type&gt;) -&gt; &lt;numeric type&gt;</span>
<span class="token operator">&amp;</span><span class="token punctuation">,</span> <span class="token operator">||</span><span class="token punctuation">,</span> <span class="token operator">-&gt;</span><span class="token punctuation">,</span> <span class="token operator">&lt;-&gt;</span>    <span class="token comment">-- (Bool, Bool) -&gt;</span>
<span class="token operator">=</span><span class="token punctuation">,</span>                <span class="token comment">-- (&lt;any type&gt;, &gt;any type&gt;) -&gt; Bool</span>
<span class="token operator">~</span><span class="token punctuation">,</span>                <span class="token comment">-- Bool -&gt; Bool</span>
<span class="token operator">&gt;=</span><span class="token punctuation">,</span> <span class="token operator">&lt;=</span><span class="token punctuation">,</span> <span class="token operator">&lt;</span><span class="token punctuation">,</span> <span class="token operator">&gt;</span>      <span class="token comment">-- (&lt;numeric type&gt;, &lt;numeric type&gt;) -&gt; Bool</span>
<span class="token constant">List1</span> <span class="token operator">++</span> <span class="token constant">List2</span><span class="token punctuation">,</span>
<span class="token hvariable">a</span><span class="token operator">:</span><span class="token constant">List</span>            <span class="token comment">-- (T, List&lt;T&gt;) -&gt; List&lt;T&gt;</span>
</code></pre>
<p>The Haskell backtick syntax can also be used. For any binary prefix function <code>f</code>:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token number">1</span> <span class="token operator">\`f\`</span> <span class="token number">2</span> <span class="token operator">=</span> <span class="token hvariable">f</span><span class="token punctuation">(</span><span class="token number">1</span><span class="token punctuation">,</span> <span class="token number">2</span><span class="token punctuation">)</span>
</code></pre>
<p>We also have the boolean literals</p>
<pre class=" language-java"><code class="prism  language-java"><span class="token boolean">true</span>     <span class="token boolean">false</span>
</code></pre>
<p>We also have the <code>in</code> operator on sets which acts as syntactic sugar for predicate application</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">S</span> <span class="token operator">::</span> <span class="token constant">Set</span><span class="token operator">&lt;</span><span class="token constant">Int</span><span class="token operator">&gt;</span>
<span class="token number">3</span> <span class="token keyword">in</span> <span class="token constant">S</span>           <span class="token comment">-- equivalent to   S(3)</span>
</code></pre>
<p>Some example formulae to give an idea of what they look like:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">]</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">,</span> <span class="token hvariable">y</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token hvariable">x</span> <span class="token operator">&gt;</span> <span class="token hvariable">y</span> <span class="token operator">-&gt;</span> <span class="token constant">EX</span> <span class="token punctuation">(</span><span class="token hvariable">n</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token hvariable">x</span> <span class="token operator">+</span> <span class="token hvariable">n</span> <span class="token operator">&gt;</span> <span class="token hvariable">y</span><span class="token punctuation">]</span><span class="token punctuation">]</span>
</code></pre>
<p>Quantifiers and other commonly used logical symbols will be displayed in iProve using the appropriate symbols, but to make keyboard typing easier, the syntax is entirely ASCII characters</p>
<h3 id="lists-and-tuples">Lists and Tuples</h3>
<p>List literals can be written:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token punctuation">{</span> <span class="token number">1</span><span class="token punctuation">,</span> <span class="token number">2</span><span class="token punctuation">,</span> <span class="token number">3</span> <span class="token punctuation">}</span>         <span class="token comment">-- C-style</span>
<span class="token punctuation">[</span> <span class="token number">1</span><span class="token punctuation">,</span> <span class="token number">2</span><span class="token punctuation">,</span> <span class="token number">3</span> <span class="token punctuation">]</span>         <span class="token comment">-- Haskell-style</span>
<span class="token punctuation">[</span> <span class="token number">1</span><span class="token punctuation">,</span> <span class="token punctuation">]</span>              <span class="token comment">-- to differentiate singleton lists from parenthesized terms</span>
<span class="token constant">List</span><span class="token operator">&lt;</span><span class="token constant">Int</span><span class="token operator">&gt;</span><span class="token punctuation">(</span><span class="token number">1</span><span class="token punctuation">,</span><span class="token number">2</span><span class="token punctuation">,</span><span class="token number">3</span><span class="token punctuation">)</span>    <span class="token comment">-- to annotate type</span>
<span class="token constant">List</span><span class="token operator">&lt;</span><span class="token constant">Int</span><span class="token operator">&gt;</span><span class="token punctuation">(</span><span class="token punctuation">)</span>         <span class="token comment">-- the only allowed syntax for empty lists, since otherwise sort cannot be determined</span>
</code></pre>
<p>Atomic literals are also extended by the list index operation:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">list</span><span class="token punctuation">[</span><span class="token builtin">index</span><span class="token punctuation">]</span>          <span class="token comment">-- returns element index of list</span>
<span class="token hvariable">list</span><span class="token punctuation">[</span><span class="token hvariable">i</span><span class="token punctuation">]</span><span class="token punctuation">[</span><span class="token hvariable">j</span><span class="token punctuation">]</span><span class="token punctuation">[</span><span class="token hvariable">k</span><span class="token punctuation">]</span>        <span class="token comment">-- can be stacked</span>
</code></pre>
<p>and the list slice operation:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">list</span><span class="token punctuation">[</span><span class="token hvariable">start_idx</span><span class="token operator">..</span><span class="token hvariable">end_idx</span><span class="token punctuation">)</span>    <span class="token comment">-- returns the sublist from start_idx inclusive to end_idx exclusive</span>
<span class="token hvariable">list</span><span class="token punctuation">[</span><span class="token hvariable">i</span><span class="token operator">..</span><span class="token hvariable">j</span><span class="token punctuation">)</span><span class="token punctuation">[</span><span class="token hvariable">k</span><span class="token operator">..</span><span class="token hvariable">l</span><span class="token punctuation">)</span><span class="token punctuation">[</span><span class="token hvariable">m</span><span class="token punctuation">]</span>         <span class="token comment">-- can be stacked</span>
</code></pre>
<p>Tuple literals must be explicitly stated via their constructor:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">Tuple</span><span class="token punctuation">(</span><span class="token hvariable">a</span><span class="token punctuation">,</span><span class="token hvariable">b</span><span class="token punctuation">,</span><span class="token hvariable">c</span><span class="token punctuation">)</span>
</code></pre>
<p>There is no shorthand for singleton tuples, these should be constructed with <code>Tuple(a)</code></p>
<p>Builtin functions on lists and tuples are given by:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token builtin">head</span><span class="token punctuation">(</span><span class="token hvariable">list</span><span class="token punctuation">)</span>      <span class="token comment">-- returns the first element of a list</span>
<span class="token builtin">tail</span><span class="token punctuation">(</span><span class="token hvariable">list</span><span class="token punctuation">)</span>      <span class="token comment">-- returns the substring of the list from the second element onwards</span>

<span class="token hvariable">a</span><span class="token operator">:</span><span class="token hvariable">list</span>          <span class="token comment">-- returns list with a consed to the front</span>
<span class="token hvariable">list1</span> <span class="token operator">++</span> <span class="token hvariable">list2</span>  <span class="token comment">-- returns list1 concatenated with list2</span>

<span class="token builtin">fst</span><span class="token punctuation">(</span><span class="token hvariable">tuple</span><span class="token punctuation">)</span>      <span class="token comment">-- first element</span>
<span class="token builtin">snd</span><span class="token punctuation">(</span><span class="token hvariable">tuple</span><span class="token punctuation">)</span>      <span class="token comment">-- second element</span>
<span class="token hvariable">elem3</span><span class="token punctuation">(</span><span class="token hvariable">tuple</span><span class="token punctuation">)</span>     <span class="token comment">-- third element</span>
<span class="token hvariable">elemN</span><span class="token punctuation">(</span><span class="token hvariable">tuple</span><span class="token punctuation">)</span>     <span class="token comment">-- Nth element</span>
</code></pre>
<h3 id="inductive-types">Inductive types</h3>
<p>Inductively defined type parameters can be written as atoms via calls to their constructors intuitively enough:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token keyword">data</span> <span class="token constant">Maybe</span> <span class="token constant">T</span> <span class="token operator">=</span> <span class="token constant">Nothing</span> <span class="token operator">|</span> <span class="token constant">Just</span> <span class="token constant">T</span>

<span class="token constant">Just</span><span class="token punctuation">(</span><span class="token number">9</span><span class="token punctuation">)</span> <span class="token comment">-- : Maybe&lt;Int&gt;</span>
<span class="token constant">Nothing</span> <span class="token comment">-- : Naybe&lt;Int&gt;</span>
<span class="token hvariable">get</span><span class="token punctuation">(</span><span class="token constant">Just</span><span class="token punctuation">(</span><span class="token number">9</span><span class="token punctuation">)</span><span class="token punctuation">)</span> <span class="token operator">=</span> <span class="token number">9</span>
</code></pre>
<h2 id="proof-tactics">Proof tactics</h2>
<p>When writing a proof, we often want to be able to quantify things or assume them. We are given the tactics <code>var</code>, <code>assume</code>, and <code>use</code> for this purpose. <em>(A “tactic” is just something which we can use in the proof and has no impact on the logical statements, but makes the job of proving a bit easier)</em></p>
<h4 id="var"><code>var</code></h4>
<p>We might want to work inside a quantifier. In that case we can use the var tactic to implicitly introduce them:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>             <span class="token comment">-- (1)     ass.</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">]</span>   <span class="token comment">-- (2)     ass.</span>

<span class="token hvariable">var</span> <span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span>
	<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                      <span class="token comment">-- (3)      By (1)</span>
	<span class="token constant">Q</span><span class="token punctuation">(</span><span class="token constant">X</span><span class="token punctuation">)</span>                      <span class="token comment">-- (4)      By (2), (3)</span>
<span class="token hvariable">end</span>

<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>             <span class="token comment">-- (5)      By (4)</span>
</code></pre>
<p>We cannot use the wrapped forall statement within the <code>var x</code> scope, and we cannot use <code>x</code> as a variable outside it</p>
<h4 id="assume"><code>assume</code></h4>
<p>Often, we want to prove implications. We can assume things to make this easier</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">P</span> <span class="token punctuation">(</span><span class="token constant">Zero</span><span class="token punctuation">)</span>   <span class="token operator">::=</span> <span class="token hvariable">false</span>
<span class="token constant">P</span> <span class="token punctuation">(</span><span class="token constant">Succ</span> <span class="token hvariable">i</span><span class="token punctuation">)</span> <span class="token operator">::=</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">i</span><span class="token punctuation">)</span>

<span class="token hvariable">assume</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                   <span class="token comment">-- (*)</span>
	<span class="token constant">P</span><span class="token punctuation">(</span><span class="token constant">Succ</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">)</span>                <span class="token comment">-- (1)      By (*), definition of P</span>
	<span class="token constant">P</span><span class="token punctuation">(</span><span class="token constant">Succ</span><span class="token punctuation">(</span><span class="token constant">Succ</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">)</span><span class="token punctuation">)</span>          <span class="token comment">-- (2)      By (1), definition of P</span>
<span class="token hvariable">end</span>

<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token constant">Succ</span><span class="token punctuation">(</span><span class="token constant">Succ</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">)</span><span class="token punctuation">)</span>      <span class="token comment">-- (3)      By (2)</span>
</code></pre>
<p>We can also use this to prove things when our assumptions contain OR:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">R</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                  <span class="token comment">-- (1)      ass.</span>
<span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">R</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                  <span class="token comment">-- (2)      ass.</span>
<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">||</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                  <span class="token comment">-- (3)      ass.</span>

<span class="token hvariable">assume</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                   <span class="token comment">-- (*)</span>
	<span class="token constant">R</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                      <span class="token comment">-- (4)      By (*), (1)</span>
<span class="token hvariable">end</span>
<span class="token hvariable">assume</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                   <span class="token comment">-- (**)</span>
	<span class="token constant">R</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                      <span class="token comment">-- (5)      By (**), (2)</span>
<span class="token hvariable">end</span>

<span class="token constant">R</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                          <span class="token comment">-- (6)      By (3), (4), (6)</span>
</code></pre>
<p>Note that this is implicitly deriving <code>R(x)</code> from:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token punctuation">[</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">R</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">]</span> <span class="token operator">&amp;</span> <span class="token punctuation">[</span><span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">R</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">]</span> <span class="token operator">&amp;</span> <span class="token punctuation">[</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">||</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">]</span>
</code></pre>
<p>Z3 is just smart enough to know that this implies <code>R(x)</code>. In this case, the <code>assume</code> statement has done nothing to the underlying logic, but for more complex formulae it can be useful</p>
<h4 id="use"><code>use</code></h4>
<p>Commonly, we want to prove something about a variable wrapped in an <code>exists</code> quantifier. We provide the <code>use</code> tactic:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">EX</span> <span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token operator">:</span><span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>               <span class="token comment">-- (1)      ass.</span>
<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                  <span class="token comment">-- (2)      ass.</span>

<span class="token hvariable">use</span> <span class="token constant">EX</span> <span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token operator">:</span><span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>           <span class="token comment">-- (*)</span>
	<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                      <span class="token comment">-- (3)      By (*)</span>
	<span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                      <span class="token comment">-- (4)      By (2), (3)</span>
<span class="token hvariable">end</span>

<span class="token constant">EX</span> <span class="token punctuation">(</span><span class="token hvariable">y</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">y</span><span class="token punctuation">)</span>             <span class="token comment">-- (5)      By (1), (4)</span>
</code></pre>
<p><code>use</code> is in fact shorthand for two tactics combined, and the final step of deriving the exists statement is done by the underlying solver. The above is equivalent to:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">EX</span> <span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token operator">:</span><span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>               <span class="token comment">-- (1)      ass.</span>
<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                  <span class="token comment">-- (2)      ass.</span>

<span class="token hvariable">var</span> <span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span>                   <span class="token comment">-- (*)</span>
	<span class="token hvariable">assume</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>               <span class="token comment">-- (**)</span>
		<span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                  <span class="token comment">-- (3)      By (**), (2)</span>
	<span class="token hvariable">end</span>
<span class="token hvariable">end</span>

<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token operator">:</span><span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span><span class="token punctuation">]</span>     <span class="token comment">-- (4)      By (3)</span>
<span class="token constant">EX</span> <span class="token punctuation">(</span><span class="token hvariable">y</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">Q</span><span class="token punctuation">(</span><span class="token hvariable">y</span><span class="token punctuation">)</span>             <span class="token comment">-- (5)      By (1), (4)</span>
</code></pre>
<h4 id="pure-variables"><code>pure</code> variables</h4>
<p>When declaring a variable in the globals box, there is a third keyword that can be used:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">pure</span> <span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span>
</code></pre>
<p>A <code>pure</code> variable is one which always remains uninterpreted. That is to say, consider the following proof:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token comment">-- global declarations:</span>
<span class="token hvariable">var</span> <span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span>

<span class="token comment">-- proof steps:</span>
<span class="token comment">-- ...</span>
<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                <span class="token comment">-- proven from statements above</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">y</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">y</span><span class="token punctuation">)</span>   <span class="token comment">-- CANNOT BE DERIVED</span>
</code></pre>
<p>Note that we have made no assumptions about <code>x</code>. The last statement does hold because we have taken <code>x</code> arbitrary, but this cannot be proven. Since it is a global variable and not introduced by a tacic, we cannot be certain that formulae elsewhere in the proof don’t place conditions on what <code>x</code> can be. To counter this, we can declare <code>x</code> as <code>pure</code>. Every formula in which <code>x</code> appears will now be invisibly wrapped in <code>FA (x: Int)</code></p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token comment">-- global declarations:</span>
<span class="token hvariable">pure</span> <span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Int</span>

<span class="token comment">-- proof steps:</span>
<span class="token comment">-- ...</span>
<span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>                <span class="token comment">-- proven from statements above. Implicitly equivalent to FA (x: Int).P(x)</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">y</span> <span class="token operator">:</span> <span class="token constant">Int</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">y</span><span class="token punctuation">)</span>   <span class="token comment">-- NOW CAN BE DERIVED FROM PREVIOUS</span>
</code></pre>
<p>Pure variables can only be used in standard proof lines. They cannot form part of function definitions or similar.</p>
<h2 id="function-definitions">Function definitions</h2>
<p>An incredibly important part of reasoning about programs is the ability to define recursive functions. iProve lets us do this and use these definitions to prove facts about the functions. The syntax is as close to Haskell as possible whilst staying consistent. The main difference is that we use the <code>::=</code> directional equality operator rather than <code>=</code>.</p>
<p>We have the basic patterns:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">P</span> <span class="token hvariable">_</span>    <span class="token operator">::=</span> <span class="token hvariable">true</span>          <span class="token comment">-- the underscore pattern accepts and discards any arguments</span>
<span class="token builtin">succ</span> <span class="token hvariable">x</span> <span class="token operator">::=</span> <span class="token hvariable">x</span> <span class="token operator">+</span> <span class="token number">1</span>         <span class="token comment">-- we can write any variable name to accept any argument</span>
</code></pre>
<p>For lists, the standard patterns work as expected</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token builtin">head</span> <span class="token punctuation">(</span><span class="token hvariable">a</span> <span class="token operator">:</span> <span class="token hvariable">_</span><span class="token punctuation">)</span>  <span class="token operator">::=</span> <span class="token hvariable">a</span>
<span class="token builtin">tail</span> <span class="token punctuation">(</span><span class="token hvariable">_</span> <span class="token operator">:</span> <span class="token hvariable">as</span><span class="token punctuation">)</span> <span class="token operator">::=</span> <span class="token hvariable">as</span>
<span class="token hvariable">isEmpty</span> <span class="token punctuation">[</span><span class="token punctuation">]</span>    <span class="token operator">::=</span> <span class="token hvariable">true</span>
</code></pre>
<p>Similarly for tuples:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">elem3</span> <span class="token punctuation">(</span><span class="token hvariable">_</span><span class="token punctuation">,</span> <span class="token hvariable">_</span> <span class="token punctuation">,</span> <span class="token hvariable">a</span><span class="token punctuation">,</span> <span class="token hvariable">_</span><span class="token punctuation">)</span> <span class="token operator">::=</span> <span class="token hvariable">a</span>
</code></pre>
<p>And for inductive types:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token comment">-- data Nat = Zero | Succ Nat</span>

<span class="token hvariable">add</span> <span class="token operator">::</span> <span class="token punctuation">(</span><span class="token constant">Nat</span><span class="token punctuation">,</span> <span class="token constant">Nat</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">Nat</span>
<span class="token hvariable">add</span> <span class="token constant">Zero</span> <span class="token hvariable">i</span>     <span class="token operator">::=</span> <span class="token hvariable">i</span>
<span class="token hvariable">add</span> <span class="token punctuation">(</span><span class="token constant">Succ</span> <span class="token hvariable">j</span><span class="token punctuation">)</span> <span class="token hvariable">i</span> <span class="token operator">::=</span> <span class="token constant">Succ</span><span class="token punctuation">(</span><span class="token hvariable">add</span><span class="token punctuation">(</span><span class="token hvariable">j</span><span class="token punctuation">,</span> <span class="token hvariable">i</span><span class="token punctuation">)</span><span class="token punctuation">)</span>
</code></pre>
<p>Something you will note is that the LHS of these statements uses Haskell-style function syntax where parameters are space-separated from functions, where as the RHS uses FOL-style function syntax. We wanted to keep pattern matching as familiar as possible, but Haskell takes its application syntax from Lambda calculus rather than FOL, hence we settled on this compromise.</p>
<p>All patterns can be stacked:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">complexFn</span> <span class="token operator">::</span> <span class="token punctuation">[</span><span class="token constant">Maybe</span><span class="token operator">&lt;</span><span class="token constant">Nat</span><span class="token operator">&gt;</span><span class="token punctuation">]</span> <span class="token operator">-&gt;</span> <span class="token constant">Nat</span>
<span class="token hvariable">complexFn</span> <span class="token punctuation">(</span><span class="token punctuation">(</span><span class="token constant">Just</span> <span class="token punctuation">(</span><span class="token constant">Succ</span> <span class="token hvariable">j</span><span class="token punctuation">)</span><span class="token punctuation">)</span> <span class="token operator">:</span> <span class="token hvariable">_</span><span class="token punctuation">)</span> <span class="token operator">::=</span> <span class="token hvariable">j</span>
</code></pre>
<h2 id="partial-functions">Partial functions</h2>
<p>Consider this function from before:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">complexFn</span> <span class="token operator">::</span> <span class="token punctuation">[</span><span class="token constant">Maybe</span><span class="token operator">&lt;</span><span class="token constant">Nat</span><span class="token operator">&gt;</span><span class="token punctuation">]</span> <span class="token operator">-&gt;</span> <span class="token constant">Nat</span>
<span class="token hvariable">complexFn</span> <span class="token punctuation">(</span><span class="token punctuation">(</span><span class="token constant">Just</span> <span class="token punctuation">(</span><span class="token constant">Succ</span> <span class="token hvariable">j</span><span class="token punctuation">)</span><span class="token punctuation">)</span> <span class="token operator">:</span> <span class="token hvariable">_</span><span class="token punctuation">)</span> <span class="token operator">::=</span> <span class="token hvariable">j</span>
</code></pre>
<p>This pattern is clearly incomplete. If the list is empty or the head is <code>Nothing</code>, then it will be undefined. However, the type signature asserts that, for all arguments of type <code>[Maybe&lt;Nat&gt;]</code>, it will return an element of type <code>Nat</code>. It will be very difficult to prove things about:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">complexFn</span><span class="token punctuation">(</span><span class="token constant">List</span><span class="token operator">&lt;</span><span class="token constant">Maybe</span><span class="token operator">&lt;</span><span class="token constant">Nat</span><span class="token operator">&gt;&gt;</span><span class="token punctuation">(</span><span class="token punctuation">)</span><span class="token punctuation">)</span>
</code></pre>
<p>since we know nothing about its value. But we <em>do</em> know that it will be of type <code>Nat</code>. Thus the following will hold:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">P</span> <span class="token operator">::</span> <span class="token constant">Nat</span> <span class="token operator">-&gt;</span> <span class="token constant">Bool</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Nat</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">complexFn</span><span class="token punctuation">(</span><span class="token constant">List</span><span class="token operator">&lt;</span><span class="token constant">Maybe</span><span class="token operator">&lt;</span><span class="token constant">Nat</span><span class="token operator">&gt;&gt;</span><span class="token punctuation">(</span><span class="token punctuation">)</span><span class="token punctuation">)</span><span class="token punctuation">)</span>
</code></pre>
<p>But this is perhaps not what we want. It isn’t the case that <code>complexFn(List&lt;Maybe&lt;Nat&gt;&gt;())</code> is <em>some, unknown <code>Nat</code></em>, but rather that it’s <code>undefined</code>, it does not exist.</p>
<p>For this, we can annotate the declaration with the keyword <code>partial</code>:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">partial</span> <span class="token hvariable">complexFn</span> <span class="token operator">::</span> <span class="token punctuation">[</span><span class="token constant">Maybe</span><span class="token operator">&lt;</span><span class="token constant">Nat</span><span class="token operator">&gt;</span><span class="token punctuation">]</span> <span class="token operator">-&gt;</span> <span class="token constant">Nat</span>
</code></pre>
<p>For a partial function, if we want to prove, for example:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token hvariable">complexFn</span><span class="token punctuation">(</span><span class="token constant">X</span><span class="token punctuation">)</span> <span class="token operator">=</span> <span class="token hvariable">complexFn</span><span class="token punctuation">(</span><span class="token constant">Y</span><span class="token punctuation">)</span>
</code></pre>
<p>we also must prove that both of these things are defined. This leads to a common trick when we want to prove things about partial functions. Let’s say im only interested in objects of type <code>[Maybe&lt;Nat&gt;]</code> when they are nonempty and their head is not <code>Nothing</code>. In this case, I might want to prove</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token constant">X</span> <span class="token operator">:</span> <span class="token punctuation">[</span><span class="token constant">Maybe</span><span class="token operator">&lt;</span><span class="token constant">Nat</span><span class="token operator">&gt;</span><span class="token punctuation">]</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">complexFn</span><span class="token punctuation">(</span><span class="token constant">X</span><span class="token punctuation">)</span><span class="token punctuation">)</span>
</code></pre>
<p>However this will always be untrue with the current definition. To achieve what I want, I can simply change my formula to:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token constant">X</span> <span class="token operator">:</span> <span class="token punctuation">[</span><span class="token constant">Maybe</span><span class="token operator">&lt;</span><span class="token constant">Nat</span><span class="token operator">&gt;</span><span class="token punctuation">]</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span> <span class="token constant">EX</span> <span class="token punctuation">(</span><span class="token hvariable">n</span> <span class="token operator">:</span> <span class="token constant">Nat</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token hvariable">complexFn</span><span class="token punctuation">(</span><span class="token constant">X</span><span class="token punctuation">)</span> <span class="token operator">=</span> <span class="token hvariable">n</span> <span class="token operator">-&gt;</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">n</span><span class="token punctuation">)</span><span class="token punctuation">]</span> <span class="token punctuation">]</span>
</code></pre>
<p>This says <strong>for all X, <em>if</em> complexFn(X) is defined, <em>then</em> P(complexFn(X))</strong>, which it is possible to prove!</p>
<h2 id="induction">Induction</h2>
<p>One of the most powerful aspects of iProve is the ability to prove facts by induction.</p>
<h3 id="bounded-ints">Bounded <code>Int</code>s</h3>
<p>Often, we want to quantify over integers defined by a particular bound. We have syntactical sugar for this:</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">&gt;=</span> <span class="token number">6</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>           <span class="token comment">-- FA(x : Int).[x &gt;= 6 -&gt; P(x)]</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">&gt;</span> <span class="token number">5</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>            <span class="token comment">-- FA(x : Int).[x &gt; 5 -&gt; P(x)]</span>
</code></pre>
<p>In this case, the variable name must come first, followed by the bound. Only one bound can be specified in the quantifier.</p>
<p>This is particularly useful in induction. Bounded <code>Int</code>s are inductively defined types, unbounded <code>Int</code>s are not since they have no base case. We can of course induct over <code>Int</code>s by inducting over <code>x &lt; 0</code> and <code>x &gt;= 0</code> seperately, for example.</p>
<p>If the bound given on an int is from above, then the inductive steps will be <code>P(x) -&gt; P(x - 1)</code>, and if it is given from below the inductive steps will be <code>P(x) -&gt; P(x + 1)</code>. If the bound is not strict, the base case will be <code>P(bound)</code>, if it is strict the base case will be <code>P(bound +/- 1)</code>.</p>
<p>Note that there is no type for natural numbers builtin to iProve. <code>n &gt;= 0</code> can be used to maintain normal mathematical operations, or a user-defined inductive type can be used otherwise.</p>
<h3 id="inductive-setup">Inductive setup</h3>
<p>Consider the following setup:</p>
<pre><code>data Nat = Zero | Succ Nat
P :: Nat -&gt; Bool
P Zero     ::= true
P (Succ n) ::= P(n)
</code></pre>
<p>Clearly, <code>P(n)</code> always holds, however iProve’s underlying solver will be unable to make any progress on proving this as it cannot generate inductive principles itself. However, we can help it out. An induction node has four fields:</p>
<ul>
<li><strong>Types</strong>: Here we simply list the inductive types we will be ranging over</li>
<li><strong>Motives</strong>: We enter the statements we want to prove in these fields. They must be of the form <code>FA (x : T).Term</code> for some <code>T</code> selected in the types box. If <code>T = Int</code>, then a bound must be specified on <code>x</code> (the variable can be called anything). The induction principle will be generated for this motive. If multiple mutually-inductive motives are to be proven, put each of them in the motives box.</li>
<li><strong>Base cases</strong>: Enter each base case to be proven here</li>
<li><strong>Inductive cases</strong>: Enter each inductive case to be proven here. These will be of the form <code>FA (x:T).[induction hypothesis -&gt; what is to be proven]</code><br>
We can now ask iProve to check whether our principle is correct. First, it will generate its own principle through a recursor-generation algorithm. Next, it will conjunct the base cases, inductive cases and motives you entered and ask whether</li>
</ul>
<pre><code>phi ::= &lt;base cases&gt; &amp; &lt;inductive cases&gt; -&gt; &lt;motives&gt;
</code></pre>
<p>is equivalent to the principle it generated. If it is, the node will turn green, otherwise it will turn red, indicating it is unsafe to be used in proofs as you have not specified the correct principle.</p>
<p>The inductive node will now act as a satisfied proof node with:</p>
<pre><code>givens      = &lt;base cases&gt; &amp; &lt;inductive cases&gt;
goal        = &lt;motives&gt;
</code></pre>
<p>And can be used in proofs accordingly.</p>
<p>For completeness, we can describe the entries for the setup at the start of this section</p>
<pre class=" language-haskell"><code class="prism  language-haskell"><span class="token comment">-- Types</span>
<span class="token keyword">data</span> <span class="token constant">Nat</span> <span class="token operator">=</span> <span class="token constant">Zero</span> <span class="token operator">|</span> <span class="token constant">Succ</span> <span class="token constant">Nat</span>

<span class="token comment">-- Base cases</span>
<span class="token constant">P</span><span class="token punctuation">(</span><span class="token constant">Zero</span><span class="token punctuation">)</span>

<span class="token comment">-- Inductive cases</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">n</span> <span class="token operator">:</span> <span class="token constant">Nat</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token punctuation">[</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">n</span><span class="token punctuation">)</span> <span class="token operator">-&gt;</span> <span class="token constant">P</span><span class="token punctuation">(</span><span class="token constant">Succ</span><span class="token punctuation">(</span><span class="token hvariable">n</span><span class="token punctuation">)</span><span class="token punctuation">)</span><span class="token punctuation">]</span>

<span class="token comment">-- Motives</span>
<span class="token constant">FA</span> <span class="token punctuation">(</span><span class="token hvariable">x</span> <span class="token operator">:</span> <span class="token constant">Nat</span><span class="token punctuation">)</span><span class="token punctuation">.</span><span class="token constant">P</span><span class="token punctuation">(</span><span class="token hvariable">x</span><span class="token punctuation">)</span>
</code></pre>

    </div>
  </div>
</body>

</html>`
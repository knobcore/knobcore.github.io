/* PulsePoint Strategies — interactions (vanilla JS, no dependencies) */
(function () {
  "use strict";

  /* ---- Mobile nav toggle ---- */
  var toggle = document.querySelector(".nav-toggle");
  var body = document.body;
  if (toggle) {
    toggle.addEventListener("click", function () {
      var open = body.classList.toggle("nav-open");
      toggle.setAttribute("aria-expanded", open ? "true" : "false");
    });
    // close menu when a link is tapped
    document.querySelectorAll(".nav a").forEach(function (a) {
      a.addEventListener("click", function () {
        body.classList.remove("nav-open");
        toggle.setAttribute("aria-expanded", "false");
      });
    });
  }

  /* ---- Sticky header shadow on scroll ---- */
  var header = document.querySelector(".site-header");
  if (header) {
    var onScroll = function () {
      header.classList.toggle("is-scrolled", window.scrollY > 12);
    };
    onScroll();
    window.addEventListener("scroll", onScroll, { passive: true });
  }

  /* ---- Reveal on scroll ---- */
  var reveals = document.querySelectorAll(".reveal");
  if ("IntersectionObserver" in window && reveals.length) {
    var io = new IntersectionObserver(function (entries) {
      entries.forEach(function (e) {
        if (e.isIntersecting) {
          e.target.classList.add("is-in");
          io.unobserve(e.target);
        }
      });
    }, { threshold: 0.12, rootMargin: "0px 0px -40px 0px" });
    reveals.forEach(function (el) { io.observe(el); });
  } else {
    reveals.forEach(function (el) { el.classList.add("is-in"); });
  }

  /* ---- Count-up stats ---- */
  var counters = document.querySelectorAll("[data-count]");
  if ("IntersectionObserver" in window && counters.length) {
    var cio = new IntersectionObserver(function (entries) {
      entries.forEach(function (e) {
        if (!e.isIntersecting) return;
        var el = e.target;
        cio.unobserve(el);
        var target = parseFloat(el.getAttribute("data-count"));
        var suffix = el.getAttribute("data-suffix") || "";
        var decimals = (target % 1 !== 0) ? 1 : 0;
        var dur = 1400, start = null;
        var step = function (ts) {
          if (!start) start = ts;
          var p = Math.min((ts - start) / dur, 1);
          var eased = 1 - Math.pow(1 - p, 3);
          el.textContent = (target * eased).toFixed(decimals) + suffix;
          if (p < 1) requestAnimationFrame(step);
          else el.textContent = target.toFixed(decimals) + suffix;
        };
        requestAnimationFrame(step);
      });
    }, { threshold: 0.5 });
    counters.forEach(function (c) { cio.observe(c); });
  }

  /* ---- Partners carousel (prev/next + dots + auto-advance) ---- */
  var pcarTrack = document.getElementById("pcar-track");
  if (pcarTrack) {
    var pcar = pcarTrack.closest(".pcar");
    var slides = Array.prototype.slice.call(pcarTrack.children);
    var dotsWrap = document.getElementById("pcar-dots");
    var prevBtn = pcar.querySelector(".pcar__btn--prev");
    var nextBtn = pcar.querySelector(".pcar__btn--next");
    var idx = 0, timer = null;

    slides.forEach(function (_, n) {
      var d = document.createElement("button");
      d.className = "pcar__dot";
      d.type = "button";
      d.setAttribute("aria-label", "Go to partner " + (n + 1));
      d.addEventListener("click", function () { go(n); restart(); });
      dotsWrap.appendChild(d);
    });
    var dots = Array.prototype.slice.call(dotsWrap.children);

    function go(n) {
      idx = (n + slides.length) % slides.length;
      pcarTrack.style.transform = "translateX(" + (-idx * 100) + "%)";
      dots.forEach(function (d, i) { d.classList.toggle("is-active", i === idx); });
    }
    function restart() {
      if (timer) clearInterval(timer);
      timer = setInterval(function () { go(idx + 1); }, 4000);
    }
    if (prevBtn) prevBtn.addEventListener("click", function () { go(idx - 1); restart(); });
    if (nextBtn) nextBtn.addEventListener("click", function () { go(idx + 1); restart(); });
    pcar.addEventListener("mouseenter", function () { if (timer) clearInterval(timer); });
    pcar.addEventListener("mouseleave", restart);
    // basic swipe support
    var x0 = null;
    pcarTrack.addEventListener("touchstart", function (e) { x0 = e.touches[0].clientX; }, { passive: true });
    pcarTrack.addEventListener("touchend", function (e) {
      if (x0 === null) return;
      var dx = e.changedTouches[0].clientX - x0;
      if (Math.abs(dx) > 40) { go(idx + (dx < 0 ? 1 : -1)); restart(); }
      x0 = null;
    });
    go(0); restart();
  }

  /* ---- Footer year ---- */
  var yr = document.querySelector("[data-year]");
  if (yr) yr.textContent = new Date().getFullYear();

  /* ---- Forms (static site — validate + graceful success + mailto fallback) ---- */
  document.querySelectorAll("form[data-mailto]").forEach(function (form) {
    var status = form.querySelector(".form-status");
    form.addEventListener("submit", function (ev) {
      ev.preventDefault();
      if (!form.checkValidity()) { form.reportValidity(); return; }

      var data = new FormData(form);
      var to = form.getAttribute("data-mailto");
      var subject = form.getAttribute("data-subject") || "Website enquiry";
      var lines = [];
      data.forEach(function (v, k) {
        if (k === "resume") { if (v && v.name) lines.push("Resume: " + v.name + " (please attach)"); return; }
        lines.push(k.replace(/(^|\s)\S/g, function (t) { return t.toUpperCase(); }) + ": " + v);
      });
      var mailto = "mailto:" + to +
        "?subject=" + encodeURIComponent(subject) +
        "&body=" + encodeURIComponent(lines.join("\n"));

      if (status) {
        status.className = "form-status is-ok";
        status.innerHTML = "Thanks — your message is ready to send. Your email app should open now. " +
          "If it doesn't, email us directly at <a href='mailto:" + to + "'>" + to + "</a>.";
      }
      form.reset();
      window.location.href = mailto;
    });
  });
})();

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

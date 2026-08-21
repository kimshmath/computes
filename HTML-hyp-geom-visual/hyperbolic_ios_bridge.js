/* hyperbolic_ios_bridge.js - iOS specific enhancements for Hyperbolic space */

// Force dark mode meta tag for optimal iOS experience
const metaColors = document.createElement('meta');
metaColors.name = "color-scheme";
metaColors.content = "dark";
document.head.appendChild(metaColors);

// Haptic feedback utility
function triggerHaptic(style) {
    if (window.webkit && window.webkit.messageHandlers && window.webkit.messageHandlers.nativeBridge) {
        window.webkit.messageHandlers.nativeBridge.postMessage({
            type: 'haptic',
            style: style
        });
    }
}

// Throttler for continuous events (like canvas dragging)
function throttle(func, limit) {
    let inThrottle;
    return function() {
        const args = arguments;
        const context = this;
        if (!inThrottle) {
            func.apply(context, args);
            inThrottle = true;
            setTimeout(() => inThrottle = false, limit);
        }
    }
}

const throttledSelection = throttle(() => triggerHaptic('selection'), 150);
const throttledLight = throttle(() => triggerHaptic('light'), 100);

document.addEventListener("DOMContentLoaded", () => {
    // 1. Point placement and buttons (Light impact)
    const btnDraw = document.getElementById('btnDraw');
    const btnParallel = document.getElementById('btnParallel');
    const parallelCanvas = document.getElementById('parallelCanvas');

    if (btnDraw) btnDraw.addEventListener('pointerdown', () => triggerHaptic('light'));
    if (btnParallel) btnParallel.addEventListener('pointerdown', () => triggerHaptic('light'));
    if (parallelCanvas) {
        parallelCanvas.addEventListener('pointerup', (e) => {
            // Only trigger if it was a quick click, not a drag, but the app code handles points
            // For simplicity, every release on parallel Canvas is a light click
            triggerHaptic('light');
        });
    }

    // 2. Dragging Gauss Canvas (Throttled Selection)
    const gaussCanvas = document.getElementById('gaussCanvas');
    if (gaussCanvas) {
        gaussCanvas.addEventListener('pointermove', (e) => {
            if (e.buttons > 0) throttledSelection();
        });
    }

    // 3. Tessellation Selectors (Selection)
    const pSel = document.getElementById('pSel');
    const qSel = document.getElementById('qSel');
    if (pSel) pSel.addEventListener('change', () => triggerHaptic('selection'));
    if (qSel) qSel.addEventListener('change', () => triggerHaptic('selection'));

    // 4. Teichmuller Sliders (Selection)
    ['sl_l1', 'sl_l2', 'sl_l3', 'sl_l4', 'sl_l5', 'sl_l6'].forEach(id => {
        const slider = document.getElementById(id);
        if (slider) {
            slider.addEventListener('input', throttledSelection);
        }
    });

    // 5. Moduli Space Dragging (Throttled Selection)
    const modCanvas = document.getElementById('modCanvas');
    if (modCanvas) {
        modCanvas.addEventListener('pointermove', (e) => {
            if (e.buttons > 0) throttledSelection();
        });
    }

    // 6. Walking in H3 (Light impact steps)
    const h3Btns = document.getElementById('h3Btns');
    if (h3Btns) {
        const h3btnsList = h3Btns.querySelectorAll('button');
        h3btnsList.forEach(btn => {
            btn.addEventListener('pointerdown', () => triggerHaptic('light'));
        });
    }

    // Listen to keyboard for H3 walking
    window.addEventListener('keydown', (e) => {
        const activeTag = document.activeElement ? document.activeElement.tagName : '';
        if (activeTag === 'INPUT' || activeTag === 'TEXTAREA') return;
        
        if (['w', 'a', 's', 'd', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.key)) {
            throttledLight();
        }
    });

    // Report scroll position for Narration engine syncing
    window.addEventListener("scroll", throttle(() => {
        if (window.webkit && window.webkit.messageHandlers && window.webkit.messageHandlers.nativeBridge) {
            window.webkit.messageHandlers.nativeBridge.postMessage({
                type: 'scroll',
                y: window.scrollY
            });
        }
    }, 500));
});

// Expose Narration controls to Swift Native Bridge
window.mellowMath = {
    pauseNarration: function() {
        // Handled automatically by native side mostly, but useful for interactive overrides
    },
    resumeNarration: function() {
        if (window.webkit && window.webkit.messageHandlers && window.webkit.messageHandlers.nativeBridge) {
            window.webkit.messageHandlers.nativeBridge.postMessage({
                type: 'narrationResume'
            });
        }
    }
};

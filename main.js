const palette = [
	{ id: "triangle", sides: 3, radius: 56 },
	{ id: "square", sides: 4, radius: 52 },
	{ id: "line", sides: 2, radius: 60 },
	{ id: "pentagon", sides: 5, radius: 55 },
	{ id: "hexagon", sides: 6, radius: 58 },
	{ id: "octagon", sides: 8, radius: 62 },
];

const COLOR_CHOICES = ["#ef4444", "#f97316", "#facc15", "#22c55e", "#06b6d4", "#3b82f6", "#8b5cf6", "#ec4899", "#c5cad4", "#111111"];
const DEFAULT_SHAPE_FILL = COLOR_CHOICES[Math.max(0, COLOR_CHOICES.length - 2)] || "#c5cad4";
const DEFAULT_SHAPE_STROKE = "#646d7d";
const VERTEX_SNAP_DISTANCE = 13;
const EDGE_SNAP_DISTANCE = 16;
const EDGE_ANGLE_TOLERANCE_DEG = 10;
const WORKSPACES_PER_RULE = 2;
const MIN_OUTPUT_VISIBLE_RADIUS_PX = 1.5;
const MIN_PLAY_DELAY_MS = 10;

const paletteById = new Map(palette.map((item) => [item.id, item]));
const controlsEl = document.getElementById("spawn-controls");
const clearBtn = document.getElementById("clear-btn");
const clearAllBtn = document.getElementById("clear-all-btn");
const rotateLeftBtn = document.getElementById("rotate-left-btn");
const rotateRightBtn = document.getElementById("rotate-right-btn");
const edgeAnchorDivisionsInput = document.getElementById("edge-anchor-divisions");
const edgeAnchorLabel = document.getElementById("edge-anchor-label");
const scaleDownBtn = document.getElementById("scale-down-btn");
const scaleUpBtn = document.getElementById("scale-up-btn");
const saveBtn = document.getElementById("save-btn");
const loadBtn = document.getElementById("load-btn");
const loadInput = document.getElementById("load-input");
const colorControlsEl = document.getElementById("color-controls");
const rulesContainerEl = document.getElementById("rules-container");
const outputWorkspaceEl = document.getElementById("output-workspace");
const applyRulesBtn = document.getElementById("apply-rules-btn");
const resetOutputBtn = document.getElementById("reset-output-btn");
const playRulesBtn = document.getElementById("play-rules-btn");
const toggleOutputArrowsBtn = document.getElementById("toggle-output-arrows-btn");
const toggleOutputTinyShapesBtn = document.getElementById("toggle-output-tiny-shapes-btn");
const playMaxShapesInput = document.getElementById("play-max-shapes");
const playDelayMsInput = document.getElementById("play-delay-ms");
const addRuleButtonEl = document.createElement("button");

const STORAGE_RULES_SNAPSHOT_KEY = "fracdle.rules.snapshot.v2";
const STORAGE_OUTPUT_ORIGINAL_KEY = "fracdle.output.original.v2";

const sandboxes = [];
const rules = [];
const colorSwatchButtons = [];
let activeSandbox = null;
let outputSandbox = null;
let ruleCount = 0;
let shapeClipboard = [];

const MIN_SHAPE_SCALE = 0.35;
const MAX_SHAPE_SCALE = 8;
const SCALE_STEP_UP = 1.15;
const SCALE_STEP_DOWN = 1 / SCALE_STEP_UP;

let isApplyingRules = false;
let isAutoPlaying = false;
let autoPlayRunToken = 0;
let playStoppedAtMax = false;
let outputArrowsVisible = true;
let outputTinyShapesPurged = true;
let isResettingOutput = false;
let draggingRule = null;

function regularPolygonVertices(sides, radius) {
	const points = [];
	const step = (Math.PI * 2) / sides;
	const rotationOffset = sides === 4 ? -Math.PI / 4 : 0;
	for (let i = 0; i < sides; i += 1) {
		const angle = step * i - Math.PI / 2 + rotationOffset;
		points.push({ x: Math.cos(angle) * radius, y: Math.sin(angle) * radius });
	}
	return points;
}

function toKonvaPointArray(vertices) {
	return vertices.flatMap((v) => [v.x, v.y]);
}

function degToRad(deg) {
	return (deg * Math.PI) / 180;
}

function clamp(value, min, max) {
	return Math.max(min, Math.min(max, value));
}

function hexToRgb(hex) {
	const normalizedHex = hex.replace("#", "");
	const value = Number.parseInt(normalizedHex, 16);
	if (Number.isNaN(value) || normalizedHex.length !== 6) {
		return { r: 100, g: 109, b: 125 };
	}
	return { r: (value >> 16) & 255, g: (value >> 8) & 255, b: value & 255 };
}

function rgbToHex({ r, g, b }) {
	const toHex = (n) => n.toString(16).padStart(2, "0");
	return `#${toHex(r)}${toHex(g)}${toHex(b)}`;
}

function darkenHex(hex, amount = 0.35) {
	const rgb = hexToRgb(hex);
	return rgbToHex({
		r: clamp(Math.round(rgb.r * (1 - amount)), 0, 255),
		g: clamp(Math.round(rgb.g * (1 - amount)), 0, 255),
		b: clamp(Math.round(rgb.b * (1 - amount)), 0, 255),
	});
}

function normalized(vec) {
	const len = Math.hypot(vec.x, vec.y);
	return len ? { x: vec.x / len, y: vec.y / len } : { x: 0, y: 0 };
}

function transformLocalPointToWorld(localPoint, group) {
	const angle = degToRad(group.rotation());
	const cos = Math.cos(angle);
	const sin = Math.sin(angle);
	const sx = group.scaleX() || 1;
	const sy = group.scaleY() || 1;
	const scaledX = localPoint.x * sx;
	const scaledY = localPoint.y * sy;
	const worldX = scaledX * cos - scaledY * sin + group.x();
	const worldY = scaledX * sin + scaledY * cos + group.y();
	return { x: worldX, y: worldY };
}

function wrapCoordinate(value, size) {
	if (!Number.isFinite(value) || !Number.isFinite(size) || size <= 0) {
		return value;
	}
	const wrapped = value % size;
	return wrapped < 0 ? wrapped + size : wrapped;
}

class Sandbox {
	constructor(containerEl, options = {}) {
		this.containerEl = containerEl;
		this.shapes = [];
		this.nonShadowShapeCount = 0;
		this.selectedShapeId = null;
		this.selectedShapeIds = new Set();
		this.maxShapes = Number.isFinite(options.maxShapes) ? options.maxShapes : Infinity;
		this.onShapesChanged = typeof options.onShapesChanged === "function" ? options.onShapesChanged : null;
		this.canSpawnShape = typeof options.canSpawnShape === "function" ? options.canSpawnShape : null;
		this.canChangeShapeColor =
			typeof options.canChangeShapeColor === "function" ? options.canChangeShapeColor : null;

		this.stage = new Konva.Stage({
			container: containerEl,
			width: containerEl.clientWidth,
			height: containerEl.clientHeight,
		});

		const suppressNativeDrag = (event) => {
			event.preventDefault();
		};
		this.stage.container().style.userSelect = "none";
		this.stage.container().style.webkitUserSelect = "none";
		this.stage.container().style.webkitUserDrag = "none";
		this.stage.container().style.touchAction = "none";
		this.stage.container().addEventListener("dragstart", suppressNativeDrag);
		this.stage.container().addEventListener("selectstart", suppressNativeDrag);

		this.layer = new Konva.Layer();
		this.stage.add(this.layer);

		this.selectionRect = new Konva.Rect({
			x: 0,
			y: 0,
			width: 0,
			height: 0,
			fill: "rgba(59,130,246,0.14)",
			stroke: "#3b82f6",
			strokeWidth: 1,
			visible: false,
			listening: false,
		});
		this.layer.add(this.selectionRect);

		this.dragSelectState = {
			active: false,
			additive: false,
			start: null,
			baseSelection: new Set(),
			hasDragged: false,
		};

		this.zoomState = {
			enabled: Boolean(options.enableZoom),
			level: 1,
			minLevel: 1,
			maxLevel: 5,
			zoomStep: 1.1,
			panActive: false,
			panStart: null,
		};

		this.stage.on("mousedown touchstart", (event) => {
			event.evt?.preventDefault?.();
			if (event.target === this.stage) {
				const pointer = this.stage.getPointerPosition();
				if (!pointer) {
					return;
				}
				const additive = Boolean(event.evt?.shiftKey || event.evt?.ctrlKey || event.evt?.metaKey);
				this.dragSelectState.active = true;
				this.dragSelectState.additive = additive;
				this.dragSelectState.start = { x: pointer.x, y: pointer.y };
				this.dragSelectState.baseSelection = additive ? new Set(this.selectedShapeIds) : new Set();
				this.dragSelectState.hasDragged = false;

				this.selectionRect.visible(false);
				this.selectionRect.width(0);
				this.selectionRect.height(0);
			}
			setActiveSandbox(this);
		});

		this.stage.on("mousemove touchmove", () => {
			if (!this.dragSelectState.active || !this.dragSelectState.start) {
				return;
			}
			const pointer = this.stage.getPointerPosition();
			if (!pointer) {
				return;
			}

			const dx = pointer.x - this.dragSelectState.start.x;
			const dy = pointer.y - this.dragSelectState.start.y;
			if (!this.dragSelectState.hasDragged && Math.hypot(dx, dy) < 6) {
				return;
			}
			this.dragSelectState.hasDragged = true;

			const rect = this.rectFromPoints(this.dragSelectState.start, pointer);
			this.selectionRect.position({ x: rect.x, y: rect.y });
			this.selectionRect.size({ width: rect.width, height: rect.height });
			this.selectionRect.visible(true);

			const hits = this.getShapesIntersectingRect(rect);
			const nextSelection = new Set(this.dragSelectState.baseSelection);
			hits.forEach((id) => nextSelection.add(id));
			this.setSelectedShapes([...nextSelection]);
		});

		this.stage.on("mouseup touchend", () => {
			if (!this.dragSelectState.active) {
				return;
			}

			if (!this.dragSelectState.hasDragged && !this.dragSelectState.additive) {
				this.setSelectedShape(null);
			}

			this.dragSelectState.active = false;
			this.dragSelectState.start = null;
			this.dragSelectState.baseSelection = new Set();
			this.dragSelectState.hasDragged = false;
			this.selectionRect.visible(false);
			this.selectionRect.width(0);
			this.selectionRect.height(0);
			this.layer.batchDraw();
		});

		if (this.zoomState.enabled) {
			this._setupZoomNavigation();
		}

		this.layer.draw();
	}

	rectFromPoints(a, b) {
		return {
			x: Math.min(a.x, b.x),
			y: Math.min(a.y, b.y),
			width: Math.abs(b.x - a.x),
			height: Math.abs(b.y - a.y),
		};
	}

	rectsIntersect(a, b) {
		return !(
			a.x + a.width < b.x ||
			b.x + b.width < a.x ||
			a.y + a.height < b.y ||
			b.y + b.height < a.y
		);
	}

	pointInRect(point, rect) {
		return (
			point.x >= rect.x &&
			point.x <= rect.x + rect.width &&
			point.y >= rect.y &&
			point.y <= rect.y + rect.height
		);
	}

	pointInPolygon(point, polygon) {
		let inside = false;
		for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i, i += 1) {
			const xi = polygon[i].x;
			const yi = polygon[i].y;
			const xj = polygon[j].x;
			const yj = polygon[j].y;
			const intersects =
				yi > point.y !== yj > point.y &&
				point.x < ((xj - xi) * (point.y - yi)) / ((yj - yi) || Number.EPSILON) + xi;
			if (intersects) {
				inside = !inside;
			}
		}
		return inside;
	}

	segmentsIntersect(a1, a2, b1, b2) {
		const orientation = (p, q, r) => {
			const value = (q.y - p.y) * (r.x - q.x) - (q.x - p.x) * (r.y - q.y);
			if (Math.abs(value) < 1e-9) {
				return 0;
			}
			return value > 0 ? 1 : 2;
		};

		const onSegment = (p, q, r) => {
			return (
				q.x <= Math.max(p.x, r.x) &&
				q.x >= Math.min(p.x, r.x) &&
				q.y <= Math.max(p.y, r.y) &&
				q.y >= Math.min(p.y, r.y)
			);
		};

		const o1 = orientation(a1, a2, b1);
		const o2 = orientation(a1, a2, b2);
		const o3 = orientation(b1, b2, a1);
		const o4 = orientation(b1, b2, a2);

		if (o1 !== o2 && o3 !== o4) {
			return true;
		}

		if (o1 === 0 && onSegment(a1, b1, a2)) {
			return true;
		}
		if (o2 === 0 && onSegment(a1, b2, a2)) {
			return true;
		}
		if (o3 === 0 && onSegment(b1, a1, b2)) {
			return true;
		}
		if (o4 === 0 && onSegment(b1, a2, b2)) {
			return true;
		}

		return false;
	}

	polygonIntersectsRect(polygon, rect) {
		if (!Array.isArray(polygon) || polygon.length < 3) {
			return false;
		}

		if (polygon.some((point) => this.pointInRect(point, rect))) {
			return true;
		}

		const rectCorners = [
			{ x: rect.x, y: rect.y },
			{ x: rect.x + rect.width, y: rect.y },
			{ x: rect.x + rect.width, y: rect.y + rect.height },
			{ x: rect.x, y: rect.y + rect.height },
		];
		if (rectCorners.some((corner) => this.pointInPolygon(corner, polygon))) {
			return true;
		}

		const rectEdges = [
			[rectCorners[0], rectCorners[1]],
			[rectCorners[1], rectCorners[2]],
			[rectCorners[2], rectCorners[3]],
			[rectCorners[3], rectCorners[0]],
		];
		for (let i = 0; i < polygon.length; i += 1) {
			const a = polygon[i];
			const b = polygon[(i + 1) % polygon.length];
			for (const [r1, r2] of rectEdges) {
				if (this.segmentsIntersect(a, b, r1, r2)) {
					return true;
				}
			}
		}

		return false;
	}

	lineIntersectsRect(linePoints, rect) {
		if (!Array.isArray(linePoints) || linePoints.length !== 2) {
			return false;
		}

		const [a, b] = linePoints;
		if (this.pointInRect(a, rect) || this.pointInRect(b, rect)) {
			return true;
		}

		const rectCorners = [
			{ x: rect.x, y: rect.y },
			{ x: rect.x + rect.width, y: rect.y },
			{ x: rect.x + rect.width, y: rect.y + rect.height },
			{ x: rect.x, y: rect.y + rect.height },
		];
		const rectEdges = [
			[rectCorners[0], rectCorners[1]],
			[rectCorners[1], rectCorners[2]],
			[rectCorners[2], rectCorners[3]],
			[rectCorners[3], rectCorners[0]],
		];

		for (const [r1, r2] of rectEdges) {
			if (this.segmentsIntersect(a, b, r1, r2)) {
				return true;
			}
		}

		return false;
	}

	getShapesIntersectingRect(rect) {
		const ids = [];
		for (const shape of this.shapes) {
			if (shape.isShadow) {
				continue;
			}
			if (!shape.group.listening()) {
				continue;
			}
			const polygon = this.worldVertices(shape);
			if (
				(polygon.length === 2 && this.lineIntersectsRect(polygon, rect)) ||
				(polygon.length >= 3 && this.polygonIntersectsRect(polygon, rect))
			) {
				ids.push(shape.id);
			}
		}
		return ids;
	}

	notifyShapesChanged() {
		if (typeof this.onShapesChanged === "function") {
			this.onShapesChanged(this);
		}
	}

	setShapesChangedHandler(handler) {
		this.onShapesChanged = typeof handler === "function" ? handler : null;
	}

	setActive(active) {
		this.containerEl.style.boxShadow = active ? "inset 0 0 0 3px #ff6f3c66" : "inset 0 0 0 1px #e5e9f1";
	}

	resize() {
		this.stage.width(this.containerEl.clientWidth);
		this.stage.height(this.containerEl.clientHeight);
		this.layer.batchDraw();
	}

	_setupZoomNavigation() {
		const container = this.stage.container();

		container.addEventListener("wheel", (event) => {
			if (!this.zoomState.enabled) return;
			event.preventDefault();

			const pointer = this.stage.getPointerPosition();
			if (!pointer) return;

			const direction = event.deltaY > 0 ? 0 : 1;
			const zoomFactor = direction === 1 ? this.zoomState.zoomStep : 1 / this.zoomState.zoomStep;

			this.zoomToPoint(pointer, zoomFactor);
		}, { passive: false });

		container.addEventListener("keydown", (event) => {
			if (!this.zoomState.enabled) return;

			if (event.key === "+" || event.key === "=") {
				event.preventDefault();
				const centerX = this.stage.width() / 2;
				const centerY = this.stage.height() / 2;
				this.zoomToPoint({ x: centerX, y: centerY }, this.zoomState.zoomStep);
			}

			if (event.key === "-" || event.key === "_") {
				event.preventDefault();
				const centerX = this.stage.width() / 2;
				const centerY = this.stage.height() / 2;
				this.zoomToPoint({ x: centerX, y: centerY }, 1 / this.zoomState.zoomStep);
			}

			if (event.key === "0") {
				event.preventDefault();
				this.resetZoom();
			}
		});

		let panLastPoint = null;

		container.addEventListener("mousedown", (event) => {
			if (event.button === 2 || (event.button === 1)) {
				this.zoomState.panActive = true;
				panLastPoint = { x: event.clientX, y: event.clientY };
				event.preventDefault();
			}
		});

		container.addEventListener("mousemove", (event) => {
			if (!this.zoomState.panActive || !panLastPoint) return;

			const dx = event.clientX - panLastPoint.x;
			const dy = event.clientY - panLastPoint.y;

			const stageX = this.stage.x() + dx;
			const stageY = this.stage.y() + dy;

			this.stage.position({ x: stageX, y: stageY });
			this.layer.batchDraw();

			panLastPoint = { x: event.clientX, y: event.clientY };
		});

		container.addEventListener("mouseup", () => {
			this.zoomState.panActive = false;
			panLastPoint = null;
		});

		container.addEventListener("mouseleave", () => {
			this.zoomState.panActive = false;
			panLastPoint = null;
		});
	}

	zoomToPoint(point, zoomFactor) {
		if (!this.zoomState.enabled) return;

		const oldScale = this.zoomState.level;
		const newScale = clamp(oldScale * zoomFactor, this.zoomState.minLevel, this.zoomState.maxLevel);

		if (newScale === oldScale) return;

		const scaleBy = newScale / oldScale;
		const newX = point.x - scaleBy * (point.x - this.stage.x());
		const newY = point.y - scaleBy * (point.y - this.stage.y());

		this.stage.scale({ x: newScale, y: newScale });
		this.stage.position({ x: newX, y: newY });

		this.zoomState.level = newScale;
		this.layer.batchDraw();
	}

	resetZoom() {
		if (!this.zoomState.enabled) return;

		this.stage.scale({ x: 1, y: 1 });
		this.stage.position({ x: 0, y: 0 });
		this.zoomState.level = 1;
		this.layer.batchDraw();
	}

	panBy(dx, dy) {
		if (!this.zoomState.enabled) return;

		const stageX = this.stage.x() + dx;
		const stageY = this.stage.y() + dy;

		this.stage.position({ x: stageX, y: stageY });
		this.layer.batchDraw();
	}

	getShapeById(shapeId) {
		return this.shapes.find((shape) => shape.id === shapeId) || null;
	}

	setShapeColor(shape, fillColor) {
		shape.fillColor = fillColor;
		shape.strokeColor = shape.isLine ? fillColor : darkenHex(fillColor, 0.4);
		if (shape.isLine) {
			shape.polygon.fillEnabled(false);
			shape.polygon.stroke(shape.strokeColor);
			if (shape.orientationArrow) {
				shape.orientationArrow.stroke(shape.strokeColor);
				shape.orientationArrow.fill(shape.strokeColor);
			}
		} else {
			shape.polygon.fill(shape.fillColor);
			shape.polygon.stroke(shape.strokeColor);
		}
		shape.markers.forEach((marker) => marker.stroke(shape.strokeColor));
	}

	updateShapeMarkerVisuals(shape, selected = false) {
		const groupScale = shape.group.scaleX() || 1;
		const inverseScale = groupScale !== 0 ? 1 / groupScale : 1;
		const smallScaleFactor = groupScale < 1 ? groupScale : 1;
		shape.markers.forEach((marker, idx) => {
			const markerKind = shape.markerKinds?.[idx] || "corner";
			if (markerKind === "corner") {
				marker.radius(selected ? 5 : 4);
			} else {
				marker.radius(selected ? 4 : 3);
			}
			marker.scaleX(inverseScale * smallScaleFactor);
			marker.scaleY(inverseScale * smallScaleFactor);
		});
	}

	getStrokeWidthForShape(shape, selected = false) {
		const scale = Math.abs(shape?.group?.scaleX?.() || 1);
		const adaptiveScale = clamp(scale, 0.35, 1);
		const baseWidth = selected ? 5 : 3;
		const minWidth = selected ? 0.7 : 0.45;
		return Math.max(minWidth, baseWidth * adaptiveScale);
	}

	updateShapeStrokeVisual(shape, selected = false) {
		if (!shape?.polygon) {
			return;
		}
		shape.polygon.strokeWidth(this.getStrokeWidthForShape(shape, selected));
	}

	setSelectedShape(shapeId) {
		if (shapeId == null) {
			this.selectedShapeId = null;
			this.selectedShapeIds.clear();
		} else {
			this.selectedShapeId = shapeId;
			this.selectedShapeIds = new Set([shapeId]);
		}
		this.applySelectionVisuals();
	}

	toggleSelectedShape(shapeId) {
		if (!shapeId) {
			return;
		}
		if (this.selectedShapeIds.has(shapeId)) {
			this.selectedShapeIds.delete(shapeId);
		} else {
			this.selectedShapeIds.add(shapeId);
		}
		this.selectedShapeId = this.selectedShapeIds.has(shapeId)
			? shapeId
			: this.selectedShapeIds.values().next().value || null;
		this.applySelectionVisuals();
	}

	setSelectedShapes(shapeIds) {
		this.selectedShapeIds = new Set(shapeIds.filter(Boolean));
		this.selectedShapeId = this.selectedShapeIds.values().next().value || null;
		this.applySelectionVisuals();
	}

	getSelectedShapes() {
		if (this.selectedShapeIds.size === 0) {
			return [];
		}
		return this.shapes.filter((shape) => this.selectedShapeIds.has(shape.id));
	}

	createAnchorData(vertices, edgeDivisions = 2) {
		const divisions = clamp(Number(edgeDivisions) || 2, 1, 7);
		const edgeAnchors = [];
		const edgeKinds = [];

		if (vertices.length === 2) {
			const a = vertices[0];
			const b = vertices[1];
			for (let step = 1; step < divisions; step += 1) {
				edgeAnchors.push({
					x: a.x + ((b.x - a.x) * step) / divisions,
					y: a.y + ((b.y - a.y) * step) / divisions,
				});
				edgeKinds.push(step * 2 === divisions ? "edge-midpoint" : "edge-subdivision");
			}

			return {
				anchorPoints: [...vertices, ...edgeAnchors],
				markerKinds: [...vertices.map(() => "corner"), ...edgeKinds],
				edgeDivisions: divisions,
			};
		}

		for (let i = 0; i < vertices.length; i += 1) {
			const a = vertices[i];
			const b = vertices[(i + 1) % vertices.length];
			for (let step = 1; step < divisions; step += 1) {
				edgeAnchors.push({
					x: a.x + ((b.x - a.x) * step) / divisions,
					y: a.y + ((b.y - a.y) * step) / divisions,
				});
				edgeKinds.push(step * 2 === divisions ? "edge-midpoint" : "edge-subdivision");
			}
		}

		const centerPoint = { x: 0, y: 0 };
		return {
			anchorPoints: [...vertices, ...edgeAnchors, centerPoint],
			markerKinds: [...vertices.map(() => "corner"), ...edgeKinds, "center"],
			edgeDivisions: divisions,
		};
	}

	rebuildShapeAnchors(shape, edgeDivisions) {
		if (!shape || shape.isShadow) {
			return;
		}

		const anchorData = this.createAnchorData(shape.vertices, edgeDivisions);
		shape.anchorPoints = anchorData.anchorPoints;
		shape.markerKinds = anchorData.markerKinds;
		shape.edgeAnchorDivisions = anchorData.edgeDivisions;

		shape.markers.forEach((marker) => marker.destroy());
		shape.markers = [];

		const shouldRenderMarkers = shape.group.listening();
		if (shouldRenderMarkers) {
			shape.markers = shape.anchorPoints.map((v, idx) => {
				const markerKind = shape.markerKinds[idx];
				const marker = new Konva.Circle({
					x: v.x,
					y: v.y,
					radius: markerKind === "corner" ? 4 : 3,
					fill: markerKind === "corner" ? "#ffffff" : "#e7ebf4",
					stroke: shape.strokeColor,
					strokeWidth: 2,
					listening: false,
					opacity: markerKind === "corner" ? 1 : 0.85,
				});
				shape.group.add(marker);
				return marker;
			});
		}

		this.updateShapeMarkerVisuals(shape, this.selectedShapeIds.has(shape.id));
	}

	setEdgeAnchorsForSelected(edgeDivisions) {
		const selectedShapes = this.getSelectedShapes().filter((shape) => !shape.isShadow);
		if (selectedShapes.length === 0) {
			return;
		}
		selectedShapes.forEach((shape) => this.rebuildShapeAnchors(shape, edgeDivisions));
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}

	applySelectionVisuals() {
		this.shapes.forEach((shape) => {
			const selected = this.selectedShapeIds.has(shape.id);
			this.updateShapeStrokeVisual(shape, selected);
			this.updateShapeMarkerVisuals(shape, selected);
		});
		if (activeSandbox === this) {
			updateColorButtonState();
			updateEdgeAnchorControlState();
		}
		this.layer.batchDraw();
	}

	worldVertices(shape) {
		return shape.vertices.map((v) => transformLocalPointToWorld(v, shape.group));
	}

	worldSnapPoints(shape) {
		const points = Array.isArray(shape.anchorPoints) && shape.anchorPoints.length > 0 ? shape.anchorPoints : shape.vertices;
		return points.map((p) => transformLocalPointToWorld(p, shape.group));
	}

	getClosestSnapPoint(activeShape, worldPoint, maxDistance = VERTEX_SNAP_DISTANCE) {
		if (!activeShape || !worldPoint || !Number.isFinite(worldPoint.x) || !Number.isFinite(worldPoint.y)) {
			return null;
		}

		let bestMatch = null;
		for (const candidateShape of this.shapes) {
			if (
				candidateShape.id === activeShape.id ||
				(candidateShape.isShadow && candidateShape.shadowKind !== "base-shadow")
			) {
				continue;
			}
			const candidatePoints = this.worldSnapPoints(candidateShape);
			for (const candidatePoint of candidatePoints) {
				const distance = Math.hypot(candidatePoint.x - worldPoint.x, candidatePoint.y - worldPoint.y);
				if (distance <= maxDistance && (!bestMatch || distance < bestMatch.distance)) {
					bestMatch = { point: candidatePoint, distance };
				}
			}
		}

		return bestMatch ? bestMatch.point : null;
	}

	snapScaleAnyVertexToNearbyVertex(activeShape, activeLocalPoint, anchorLocalPoint, anchorWorld, proposedScale) {
		if (!activeShape || !activeLocalPoint || !anchorLocalPoint || !anchorWorld) {
			return proposedScale;
		}

		const angle = degToRad(activeShape.group.rotation());
		const cos = Math.cos(angle);
		const sin = Math.sin(angle);

		let best = null;

		const localDelta = {
			x: activeLocalPoint.x - anchorLocalPoint.x,
			y: activeLocalPoint.y - anchorLocalPoint.y,
		};
		const deltaLenSq = localDelta.x * localDelta.x + localDelta.y * localDelta.y;
		if (deltaLenSq < 0.000001) {
			return proposedScale;
		}

		const candidatePoints = Array.isArray(activeShape.anchorPoints) && activeShape.anchorPoints.length > 0
			? activeShape.anchorPoints
			: activeShape.vertices;

		for (const activePoint of candidatePoints) {
			const pinnedDistance = Math.hypot(activePoint.x - anchorLocalPoint.x, activePoint.y - anchorLocalPoint.y);
			if (pinnedDistance < 0.001) {
				continue;
			}
			const pointDelta = {
				x: activePoint.x - anchorLocalPoint.x,
				y: activePoint.y - anchorLocalPoint.y,
			};
			const worldDeltaScaleOne = {
				x: pointDelta.x * cos - pointDelta.y * sin,
				y: pointDelta.x * sin + pointDelta.y * cos,
			};
			const pointLenSq = worldDeltaScaleOne.x * worldDeltaScaleOne.x + worldDeltaScaleOne.y * worldDeltaScaleOne.y;
			if (pointLenSq < 0.000001) {
				continue;
			}

			const proposedWorld = {
				x: anchorWorld.x + worldDeltaScaleOne.x * proposedScale,
				y: anchorWorld.y + worldDeltaScaleOne.y * proposedScale,
			};

			for (const candidateShape of this.shapes) {
				if (
					candidateShape.id === activeShape.id ||
					(candidateShape.isShadow && candidateShape.shadowKind !== "base-shadow")
				) {
					continue;
				}
				const candidatePoints = this.worldSnapPoints(candidateShape);
				for (const candidateVertex of candidatePoints) {
					const pinnedCandidateDistance = Math.hypot(
						candidateVertex.x - anchorWorld.x,
						candidateVertex.y - anchorWorld.y,
					);
					if (pinnedCandidateDistance < 0.001) {
						continue;
					}
					const distanceToProposed = Math.hypot(
						candidateVertex.x - proposedWorld.x,
						candidateVertex.y - proposedWorld.y,
					);
					if (distanceToProposed > VERTEX_SNAP_DISTANCE) {
						continue;
					}

					const rel = {
						x: candidateVertex.x - anchorWorld.x,
						y: candidateVertex.y - anchorWorld.y,
					};
					const projectedScale =
						(rel.x * worldDeltaScaleOne.x + rel.y * worldDeltaScaleOne.y) / pointLenSq;
					const clampedScale = clamp(projectedScale, MIN_SHAPE_SCALE, MAX_SHAPE_SCALE);
					const snappedWorld = {
						x: anchorWorld.x + worldDeltaScaleOne.x * clampedScale,
						y: anchorWorld.y + worldDeltaScaleOne.y * clampedScale,
					};
					const snapError = Math.hypot(
						candidateVertex.x - snappedWorld.x,
						candidateVertex.y - snappedWorld.y,
					);
					if (snapError > VERTEX_SNAP_DISTANCE) {
						continue;
					}

					if (!best || snapError < best.error) {
						best = { scale: clampedScale, error: snapError };
					}
				}
			}
		}

		return best ? best.scale : proposedScale;
	}

	worldEdges(shape) {
		const vertices = this.worldVertices(shape);
		if (vertices.length === 2) {
			const a = vertices[0];
			const b = vertices[1];
			return [{
				midpoint: { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 },
				dir: normalized({ x: b.x - a.x, y: b.y - a.y }),
			}];
		}
		const edges = [];
		for (let i = 0; i < vertices.length; i += 1) {
			const a = vertices[i];
			const b = vertices[(i + 1) % vertices.length];
			edges.push({
				midpoint: { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 },
				dir: normalized({ x: b.x - a.x, y: b.y - a.y }),
			});
		}
		return edges;
	}

	deleteShapeById(shapeId) {
		const index = this.shapes.findIndex((shape) => shape.id === shapeId);
		if (index < 0) {
			return false;
		}
		const [shape] = this.shapes.splice(index, 1);
		if (!shape.isShadow) {
			this.nonShadowShapeCount = Math.max(0, this.nonShadowShapeCount - 1);
		}
		shape.group.destroy();
		this.selectedShapeIds.delete(shapeId);
		if (this.selectedShapeId === shapeId) {
			this.selectedShapeId = this.selectedShapeIds.values().next().value || null;
		}
		if (activeSandbox === this) {
			updateColorButtonState();
		}
		this.layer.batchDraw();
		this.notifyShapesChanged();
		return true;
	}

	spawnShape(config, options = {}) {
		const isShadow = Boolean(options.isShadow);
		const isReadOnly = Boolean(options.isReadOnly);
		const hideOutline = Boolean(options.hideOutline);
		const showOrientationArrow = options.showOrientationArrow !== false;
		const wrapPosition = Boolean(options.wrapPosition);
		if (!isShadow && this.canSpawnShape && !this.canSpawnShape(config, options)) {
			return null;
		}
		if (!isShadow && this.nonShadowShapeCount >= this.maxShapes) {
			return null;
		}

		const isLineShape = config.id === "line";
		const vertices = isLineShape
			? [
				{ x: -config.radius, y: 0 },
				{ x: config.radius, y: 0 },
			]
			: regularPolygonVertices(config.sides, config.radius);
		const anchorData = this.createAnchorData(vertices, Number(options.edgeAnchorDivisions) || 2);
		const anchorPoints = anchorData.anchorPoints;
		const markerKinds = anchorData.markerKinds;
		const group = new Konva.Group({
			x: wrapPosition
				? wrapCoordinate(
					options.x ?? 70 + Math.random() * Math.max(30, this.stage.width() - 140),
					this.stage.width(),
				)
				: options.x ?? 70 + Math.random() * Math.max(30, this.stage.width() - 140),
			y: wrapPosition
				? wrapCoordinate(
					options.y ?? 70 + Math.random() * Math.max(30, this.stage.height() - 140),
					this.stage.height(),
				)
				: options.y ?? 70 + Math.random() * Math.max(30, this.stage.height() - 140),
			rotation: options.rotation ?? 0,
			scaleX: Number.isFinite(Number(options.scale)) ? Number(options.scale) : 1,
			scaleY: Number.isFinite(Number(options.scale)) ? Number(options.scale) : 1,
			draggable: !isShadow && !isReadOnly,
			listening: !isShadow && !isReadOnly,
		});

		const polygon = new Konva.Line({
			points: toKonvaPointArray(vertices),
			closed: !isLineShape,
			fill: DEFAULT_SHAPE_FILL,
			stroke: isLineShape ? DEFAULT_SHAPE_FILL : DEFAULT_SHAPE_STROKE,
			hitStrokeWidth: isLineShape ? 18 : undefined,
			strokeWidth: 3,
			strokeScaleEnabled: false,
			lineJoin: "round",
			...(isReadOnly ? {} : {
				shadowColor: "#1f2633",
				shadowBlur: 8,
				shadowOffset: { x: 0, y: 2 },
				shadowOpacity: isShadow ? 0.08 : 0.2,
			}),
			opacity: isShadow ? 0.4 : 1,
		});
		if (isLineShape) {
			polygon.fillEnabled(false);
		}
		if (hideOutline && !isLineShape) {
			polygon.strokeEnabled(false);
		}
		group.add(polygon);

		const arrowTailY = config.radius * 0.2;
		const arrowHeadY = -config.radius * 0.45;
		const orientationArrow = new Konva.Arrow({
			x: 0,
			y: 0,
			points: isLineShape ? [-config.radius, 0, config.radius, 0] : [0, arrowTailY, 0, arrowHeadY],
			pointerLength: isLineShape ? Math.max(10, config.radius * 0.22) : Math.max(6, config.radius * 0.14),
			pointerWidth: isLineShape ? Math.max(8, config.radius * 0.18) : Math.max(6, config.radius * 0.14),
			stroke: isLineShape ? DEFAULT_SHAPE_FILL : "#1f2633",
			fill: isLineShape ? DEFAULT_SHAPE_FILL : "#1f2633",
			strokeWidth: 2,
			opacity: isLineShape ? (isShadow ? 0.28 : 1) : isShadow ? 0.14 : 0.2,
			listening: false,
		});
		orientationArrow.visible(showOrientationArrow);
		group.add(orientationArrow);

		const markers = isReadOnly ? [] : anchorPoints.map((v, idx) => {
			const markerKind = markerKinds[idx];
			const marker = new Konva.Circle({
				x: v.x,
				y: v.y,
				radius: isShadow ? 3 : markerKind === "corner" ? 4 : 3,
				fill: markerKind === "corner" ? "#ffffff" : "#e7ebf4",
				stroke: DEFAULT_SHAPE_STROKE,
				strokeWidth: 2,
				listening: false,
				opacity: isShadow ? 0.28 : markerKind === "corner" ? 1 : 0.85,
			});
			group.add(marker);
			return marker;
		});

		const shapeModel = {
			id: `${config.id}-${crypto.randomUUID()}`,
			typeId: config.id,
			isLine: isLineShape,
			group,
			polygon,
			orientationArrow,
			markers,
			vertices,
			anchorPoints,
			markerKinds,
			edgeAnchorDivisions: anchorData.edgeDivisions,
			fillColor: DEFAULT_SHAPE_FILL,
			strokeColor: isLineShape ? DEFAULT_SHAPE_FILL : DEFAULT_SHAPE_STROKE,
			isShadow,
			shadowKind: options.shadowKind || null,
			dragMode: "move",
			dragScaleHandleKind: null,
			dragActiveLocalPoint: null,
			dragVertexIndex: -1,
			dragEdgeMidpointIndex: -1,
			dragAnchorVertexIndex: -1,
			dragAnchorLocalPoint: null,
			dragAnchorWorld: null,
			dragStartPos: null,
			dragStartScale: 1,
			dragStartPointerDistance: 0,
			dragGroupOffsets: null,
		};

		if (typeof options.fillColor === "string") {
			this.setShapeColor(shapeModel, options.fillColor);
		}
		this.updateShapeMarkerVisuals(shapeModel, false);

		if (!isShadow && !isReadOnly) {
			group.on("mousedown touchstart", (event) => {
				event.cancelBubble = true;
				event.evt?.preventDefault?.();
				setActiveSandbox(this);
				const additiveSelect = Boolean(event.evt?.shiftKey || event.evt?.ctrlKey || event.evt?.metaKey);
				if (additiveSelect) {
					this.toggleSelectedShape(shapeModel.id);
					return;
				}
				if (!this.selectedShapeIds.has(shapeModel.id)) {
					this.setSelectedShape(shapeModel.id);
				}

				shapeModel.dragMode = "move";
				shapeModel.dragScaleHandleKind = null;
				shapeModel.dragActiveLocalPoint = null;
				shapeModel.dragVertexIndex = -1;
				shapeModel.dragEdgeMidpointIndex = -1;
				shapeModel.dragAnchorVertexIndex = -1;
				shapeModel.dragAnchorLocalPoint = null;
				shapeModel.dragAnchorWorld = null;
				const pointer = this.stage.getPointerPosition();
				if (pointer) {
					const sideCount = shapeModel.vertices.length;
					const localPoint = group.getAbsoluteTransform().copy().invert().point(pointer);
					for (let i = 0; i < shapeModel.vertices.length; i += 1) {
						const vertex = shapeModel.vertices[i];
						const dx = localPoint.x - vertex.x;
						const dy = localPoint.y - vertex.y;
						if (Math.hypot(dx, dy) <= 14) {
							shapeModel.dragMode = "scale";
							shapeModel.dragScaleHandleKind = "corner";
							shapeModel.dragVertexIndex = i;
							break;
						}
					}

					if (shapeModel.dragMode !== "scale" && sideCount > 2) {
						for (let i = 0; i < sideCount; i += 1) {
							const a = shapeModel.vertices[i];
							const b = shapeModel.vertices[(i + 1) % sideCount];
							const midpoint = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
							const dx = localPoint.x - midpoint.x;
							const dy = localPoint.y - midpoint.y;
							if (Math.hypot(dx, dy) <= 12) {
								shapeModel.dragMode = "scale";
								shapeModel.dragScaleHandleKind = "edge-midpoint";
								shapeModel.dragEdgeMidpointIndex = i;
								break;
							}
						}
					}
				}

			});

			group.on("dblclick dbltap", (event) => {
				event.cancelBubble = true;
				this.deleteShapeById(shapeModel.id);
			});

			group.on("dragstart", (event) => {
				event.evt?.preventDefault?.();
				setActiveSandbox(this);
				if (!this.selectedShapeIds.has(shapeModel.id)) {
					this.setSelectedShape(shapeModel.id);
				}
				shapeModel.dragStartPos = { ...group.position() };
				shapeModel.dragStartScale = group.scaleX() || 1;
				shapeModel.dragAnchorLocalPoint = null;
				shapeModel.dragGroupOffsets = null;

				if (shapeModel.dragMode === "move") {
					const selectedShapes = this.getSelectedShapes().filter((shape) => !shape.isShadow);
					if (selectedShapes.length > 1 && selectedShapes.some((shape) => shape.id === shapeModel.id)) {
						const startPos = shapeModel.dragStartPos;
						shapeModel.dragGroupOffsets = selectedShapes
							.filter((shape) => shape.id !== shapeModel.id)
							.map((shape) => ({
								shape,
								dx: shape.group.x() - startPos.x,
								dy: shape.group.y() - startPos.y,
							}));
					}
				}

				if (
					shapeModel.dragMode === "scale" &&
					shapeModel.dragScaleHandleKind === "corner" &&
					shapeModel.dragVertexIndex >= 0
				) {
					shapeModel.dragActiveLocalPoint = shapeModel.vertices[shapeModel.dragVertexIndex];
					const sideCount = shapeModel.vertices.length;
					const draggedIndex = shapeModel.dragVertexIndex;
					if (sideCount % 2 === 0) {
						const oppositeIndex = (draggedIndex + sideCount / 2) % sideCount;
						shapeModel.dragAnchorVertexIndex = oppositeIndex;
						shapeModel.dragAnchorLocalPoint = shapeModel.vertices[oppositeIndex];
					} else {
						const oppositeEdgeStart = (draggedIndex + Math.floor(sideCount / 2)) % sideCount;
						const a = shapeModel.vertices[oppositeEdgeStart];
						const b = shapeModel.vertices[(oppositeEdgeStart + 1) % sideCount];
						shapeModel.dragAnchorVertexIndex = -1;
						shapeModel.dragAnchorLocalPoint = {
							x: (a.x + b.x) / 2,
							y: (a.y + b.y) / 2,
						};
					}

					if (shapeModel.dragAnchorLocalPoint) {
						shapeModel.dragAnchorWorld = transformLocalPointToWorld(shapeModel.dragAnchorLocalPoint, group);
					}
				}

				if (
					shapeModel.dragMode === "scale" &&
					shapeModel.dragScaleHandleKind === "edge-midpoint" &&
					shapeModel.dragEdgeMidpointIndex >= 0
				) {
					const sideCount = shapeModel.vertices.length;
					const midpointIndex = shapeModel.dragEdgeMidpointIndex;
					const a = shapeModel.vertices[midpointIndex];
					const b = shapeModel.vertices[(midpointIndex + 1) % sideCount];
					shapeModel.dragActiveLocalPoint = {
						x: (a.x + b.x) / 2,
						y: (a.y + b.y) / 2,
					};
					if (sideCount % 2 === 0) {
						const oppositeMidpointIndex = (midpointIndex + sideCount / 2) % sideCount;
						const c = shapeModel.vertices[oppositeMidpointIndex];
						const d = shapeModel.vertices[(oppositeMidpointIndex + 1) % sideCount];
						shapeModel.dragAnchorVertexIndex = -1;
						shapeModel.dragAnchorLocalPoint = {
							x: (c.x + d.x) / 2,
							y: (c.y + d.y) / 2,
						};
					} else {
						const oppositeIndex = (midpointIndex + Math.ceil(sideCount / 2)) % sideCount;
						shapeModel.dragAnchorVertexIndex = oppositeIndex;
						shapeModel.dragAnchorLocalPoint = shapeModel.vertices[oppositeIndex];
					}
					shapeModel.dragAnchorWorld = transformLocalPointToWorld(shapeModel.dragAnchorLocalPoint, group);
				}

				const pointer = this.stage.getPointerPosition();
				if (pointer) {
					const distanceOrigin = shapeModel.dragAnchorWorld || shapeModel.dragStartPos;
					shapeModel.dragStartPointerDistance = Math.hypot(
						pointer.x - distanceOrigin.x,
						pointer.y - distanceOrigin.y,
					);
				}
				group.moveToTop();
			});

			group.on("dragmove", () => {
				if (shapeModel.dragMode === "scale" && shapeModel.dragStartPos) {
					const pointer = this.stage.getPointerPosition();
					if (pointer) {
						if (
							shapeModel.isLine &&
							shapeModel.dragScaleHandleKind === "corner" &&
							shapeModel.dragAnchorWorld &&
							shapeModel.dragAnchorLocalPoint &&
							shapeModel.dragActiveLocalPoint
						) {
							const anchorWorld = shapeModel.dragAnchorWorld;
							const snapPoint = this.getClosestSnapPoint(shapeModel, pointer, VERTEX_SNAP_DISTANCE);
							const targetPointer = snapPoint || pointer;
							const localDelta = {
								x: shapeModel.dragActiveLocalPoint.x - shapeModel.dragAnchorLocalPoint.x,
								y: shapeModel.dragActiveLocalPoint.y - shapeModel.dragAnchorLocalPoint.y,
							};
							const baseLen = Math.hypot(localDelta.x, localDelta.y);
							const pointerDelta = {
								x: targetPointer.x - anchorWorld.x,
								y: targetPointer.y - anchorWorld.y,
							};
							const pointerLen = Math.hypot(pointerDelta.x, pointerDelta.y);

							if (baseLen > 0.000001 && pointerLen > 0.000001) {
								const localAngle = Math.atan2(localDelta.y, localDelta.x);
								const worldAngle = Math.atan2(pointerDelta.y, pointerDelta.x);
								const nextRotationDeg = ((worldAngle - localAngle) * 180) / Math.PI;
								const nextScale = clamp(pointerLen / baseLen, MIN_SHAPE_SCALE, MAX_SHAPE_SCALE);

								group.rotation(nextRotationDeg);
								group.scaleX(nextScale);
								group.scaleY(nextScale);

								const angle = degToRad(group.rotation());
								const cos = Math.cos(angle);
								const sin = Math.sin(angle);
								const anchorLocal = shapeModel.dragAnchorLocalPoint;
								const scaledX = anchorLocal.x * nextScale;
								const scaledY = anchorLocal.y * nextScale;
								const rotatedX = scaledX * cos - scaledY * sin;
								const rotatedY = scaledX * sin + scaledY * cos;
								group.position({
									x: anchorWorld.x - rotatedX,
									y: anchorWorld.y - rotatedY,
								});
							}

							this.updateShapeStrokeVisual(shapeModel, shapeModel.id === this.selectedShapeId);
							this.updateShapeMarkerVisuals(shapeModel, shapeModel.id === this.selectedShapeId);
						} else {
						const distanceOrigin = shapeModel.dragAnchorWorld || shapeModel.dragStartPos;
						const currentDistance = Math.hypot(
							pointer.x - distanceOrigin.x,
							pointer.y - distanceOrigin.y,
						);
						const startDistance = Math.max(shapeModel.dragStartPointerDistance || 1, 1);
						const scaleRatio = currentDistance / startDistance;
						let nextScale = clamp(shapeModel.dragStartScale * scaleRatio, MIN_SHAPE_SCALE, MAX_SHAPE_SCALE);

						if (shapeModel.dragAnchorWorld && shapeModel.dragAnchorLocalPoint) {
							nextScale = this.snapScaleAnyVertexToNearbyVertex(
								shapeModel,
								shapeModel.dragActiveLocalPoint,
								shapeModel.dragAnchorLocalPoint,
								shapeModel.dragAnchorWorld,
								nextScale,
							);
						}

						group.scaleX(nextScale);
						group.scaleY(nextScale);

						if (shapeModel.dragAnchorWorld && shapeModel.dragAnchorLocalPoint) {
							const anchorLocal = shapeModel.dragAnchorLocalPoint;
							const angle = degToRad(group.rotation());
							const cos = Math.cos(angle);
							const sin = Math.sin(angle);
							const scaledX = anchorLocal.x * nextScale;
							const scaledY = anchorLocal.y * nextScale;
							const rotatedX = scaledX * cos - scaledY * sin;
							const rotatedY = scaledX * sin + scaledY * cos;
							group.position({
								x: shapeModel.dragAnchorWorld.x - rotatedX,
								y: shapeModel.dragAnchorWorld.y - rotatedY,
							});
						}

						this.updateShapeStrokeVisual(shapeModel, shapeModel.id === this.selectedShapeId);
						this.updateShapeMarkerVisuals(shapeModel, shapeModel.id === this.selectedShapeId);
						}
					}
				} else if (shapeModel.dragGroupOffsets && shapeModel.dragGroupOffsets.length > 0) {
					this.snapShape(shapeModel);
					const leadPos = shapeModel.group.position();
					shapeModel.dragGroupOffsets.forEach(({ shape, dx, dy }) => {
						shape.group.position({
							x: leadPos.x + dx,
							y: leadPos.y + dy,
						});
					});
				} else {
					this.snapShape(shapeModel);
				}
				this.layer.batchDraw();
				this.notifyShapesChanged();
			});

			group.on("dragend", () => {
				shapeModel.dragMode = "move";
				shapeModel.dragScaleHandleKind = null;
				shapeModel.dragActiveLocalPoint = null;
				shapeModel.dragVertexIndex = -1;
				shapeModel.dragEdgeMidpointIndex = -1;
				shapeModel.dragAnchorVertexIndex = -1;
				shapeModel.dragAnchorLocalPoint = null;
				shapeModel.dragAnchorWorld = null;
				shapeModel.dragStartPos = null;
				shapeModel.dragStartScale = group.scaleX() || 1;
				shapeModel.dragStartPointerDistance = 0;
				shapeModel.dragGroupOffsets = null;
				this.notifyShapesChanged();
			});
		}

		this.shapes.push(shapeModel);
		this.layer.add(group);
		if (!isShadow) {
			this.nonShadowShapeCount += 1;
			if (!isReadOnly) {
				this.setSelectedShape(shapeModel.id);
				this.notifyShapesChanged();
			}
		} else {
			this.layer.batchDraw();
		}
		return shapeModel;
	}

	snapShapeToNearbyVertex(activeShape) {
		if (this.shapes.length < 2) {
			return false;
		}
		const activeVertices = this.worldSnapPoints(activeShape);
		let bestMatch = null;
		for (const candidate of this.shapes) {
			if (candidate.id === activeShape.id) {
				continue;
			}
			const candidateVertices = this.worldSnapPoints(candidate);
			for (const a of activeVertices) {
				for (const b of candidateVertices) {
					const dx = b.x - a.x;
					const dy = b.y - a.y;
					const distance = Math.hypot(dx, dy);
					if (distance <= VERTEX_SNAP_DISTANCE && (!bestMatch || distance < bestMatch.distance)) {
						bestMatch = { dx, dy, distance };
					}
				}
			}
		}
		if (!bestMatch) {
			return false;
		}
		const currentPos = activeShape.group.position();
		activeShape.group.position({ x: currentPos.x + bestMatch.dx, y: currentPos.y + bestMatch.dy });
		return true;
	}

	snapShapeToNearbyEdge(activeShape) {
		if (this.shapes.length < 2) {
			return false;
		}
		const activeEdges = this.worldEdges(activeShape);
		const maxAngleDiff = degToRad(EDGE_ANGLE_TOLERANCE_DEG);
		let bestMatch = null;
		for (const candidate of this.shapes) {
			if (candidate.id === activeShape.id) {
				continue;
			}
			const candidateEdges = this.worldEdges(candidate);
			for (const activeEdge of activeEdges) {
				for (const candidateEdge of candidateEdges) {
					const dot = activeEdge.dir.x * candidateEdge.dir.x + activeEdge.dir.y * candidateEdge.dir.y;
					const angleDiff = Math.acos(Math.abs(clamp(dot, -1, 1)));
					if (angleDiff > maxAngleDiff) {
						continue;
					}
					const dx = candidateEdge.midpoint.x - activeEdge.midpoint.x;
					const dy = candidateEdge.midpoint.y - activeEdge.midpoint.y;
					const distance = Math.hypot(dx, dy);
					if (distance <= EDGE_SNAP_DISTANCE && (!bestMatch || distance < bestMatch.distance)) {
						bestMatch = { dx, dy, distance };
					}
				}
			}
		}
		if (!bestMatch) {
			return false;
		}
		const currentPos = activeShape.group.position();
		activeShape.group.position({ x: currentPos.x + bestMatch.dx, y: currentPos.y + bestMatch.dy });
		return true;
	}

	snapShape(activeShape) {
		if (!this.snapShapeToNearbyVertex(activeShape)) {
			this.snapShapeToNearbyEdge(activeShape);
		}
	}

	rotateSelected(degrees) {
		const selectedShapes = this.getSelectedShapes().filter((shape) => !shape.isShadow);
		const activeShape = selectedShapes[0] || this.getShapeById(this.selectedShapeId);
		if (!activeShape) {
			return;
		}

		if (selectedShapes.length <= 1) {
			activeShape.group.rotation(activeShape.group.rotation() + degrees);
			this.snapShape(activeShape);
			this.notifyShapesChanged();
			return;
		}

		const center = selectedShapes.reduce(
			(acc, shape) => ({ x: acc.x + shape.group.x(), y: acc.y + shape.group.y() }),
			{ x: 0, y: 0 },
		);
		center.x /= selectedShapes.length;
		center.y /= selectedShapes.length;

		const radians = degToRad(degrees);
		selectedShapes.forEach((shape) => {
			const offset = {
				x: shape.group.x() - center.x,
				y: shape.group.y() - center.y,
			};
			const rotatedOffset = rotateVector(offset, radians);
			shape.group.position({
				x: center.x + rotatedOffset.x,
				y: center.y + rotatedOffset.y,
			});
			shape.group.rotation(shape.group.rotation() + degrees);
		});
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}

	scaleSelected(factor) {
		const activeShape = this.getShapeById(this.selectedShapeId);
		if (!activeShape) {
			return;
		}

		const currentScale = activeShape.group.scaleX() || 1;
		const nextScale = clamp(currentScale * factor, MIN_SHAPE_SCALE, MAX_SHAPE_SCALE);
		activeShape.group.scaleX(nextScale);
		activeShape.group.scaleY(nextScale);
		this.updateShapeStrokeVisual(activeShape, activeShape.id === this.selectedShapeId);
		this.updateShapeMarkerVisuals(activeShape, activeShape.id === this.selectedShapeId);
		this.snapShape(activeShape);
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}

	duplicateSelected() {
		const activeShape = this.getShapeById(this.selectedShapeId);
		if (!activeShape) {
			return;
		}

		const shapeConfig = paletteById.get(activeShape.typeId);
		if (!shapeConfig) {
			return;
		}

		const duplicate = this.spawnShape(shapeConfig, {
			x: activeShape.group.x() + 26,
			y: activeShape.group.y() + 26,
			rotation: activeShape.group.rotation(),
			scale: activeShape.group.scaleX() || 1,
			fillColor: activeShape.fillColor,
		});

		if (!duplicate) {
			return;
		}

		this.snapShape(duplicate);
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}

	deleteSelected() {
		const selectedShapes = this.getSelectedShapes().filter((shape) => !shape.isShadow);
		if (selectedShapes.length === 0) {
			const activeShape = this.getShapeById(this.selectedShapeId);
			if (activeShape && !activeShape.isShadow) {
				this.deleteShapeById(activeShape.id);
			}
			return;
		}

		selectedShapes.forEach((shape) => {
			this.deleteShapeById(shape.id);
		});
	}

	applyColorToSelected(color) {
		let targetShapes = this.getSelectedShapes().filter((shape) => !shape.isShadow);
		if (targetShapes.length === 0) {
			const activeShape = this.getShapeById(this.selectedShapeId);
			if (activeShape && !activeShape.isShadow) {
				targetShapes = [activeShape];
			}
		}

		if (targetShapes.length === 0) {
			return;
		}

		targetShapes.forEach((shape) => {
			if (this.canChangeShapeColor && !this.canChangeShapeColor(shape, color)) {
				return;
			}
			this.setShapeColor(shape, color);
		});

		this.layer.batchDraw();
		updateColorButtonState();
		this.notifyShapesChanged();
	}

	clearAllShapes(options = {}) {
		const preserveShadows = Boolean(options.preserveShadows);
		if (preserveShadows) {
			this.shapes = this.shapes.filter((shape) => {
				if (shape.isShadow) {
					return true;
				}
				shape.group.destroy();
				return false;
			});
			this.nonShadowShapeCount = 0;
		} else {
			this.shapes.forEach((shape) => shape.group.destroy());
			this.shapes.length = 0;
			this.nonShadowShapeCount = 0;
		}
		this.selectedShapeId = null;
		this.selectedShapeIds.clear();
		if (activeSandbox === this) {
			updateColorButtonState();
		}
		this.layer.batchDraw();
		this.notifyShapesChanged();
	}
}

function setActiveSandbox(sandbox) {
	activeSandbox = sandbox;
	for (const sb of sandboxes) {
		sb.setActive(sb === sandbox);
	}
	updateColorButtonState();
}

function ensureActiveSandbox() {
	if (activeSandbox) {
		return activeSandbox;
	}
	if (sandboxes.length > 0) {
		setActiveSandbox(sandboxes[0]);
		return sandboxes[0];
	}
	return null;
}

function getRotateStepDegrees(sandbox) {
	const active = sandbox || ensureActiveSandbox();
	if (!active) {
		return 15;
	}

	const selected = active.getShapeById(active.selectedShapeId);
	if (!selected) {
		return 15;
	}

	const sides = Number(selected.vertices?.length) || Number(paletteById.get(selected.typeId)?.sides) || 0;
	if (!Number.isFinite(sides) || sides < 3) {
		return 15;
	}

	return 90 / sides;
}

function copySelectionToClipboard() {
	const sandbox = ensureActiveSandbox();
	if (!sandbox) {
		return;
	}

	const selectedShapes = sandbox.getSelectedShapes().filter((shape) => !shape.isShadow);
	if (selectedShapes.length === 0) {
		const fallbackShape = sandbox.getShapeById(sandbox.selectedShapeId);
		if (!fallbackShape || fallbackShape.isShadow) {
			return;
		}
		selectedShapes.push(fallbackShape);
	}

	const center = selectedShapes.reduce(
		(acc, shape) => ({ x: acc.x + shape.group.x(), y: acc.y + shape.group.y() }),
		{ x: 0, y: 0 },
	);
	center.x /= selectedShapes.length;
	center.y /= selectedShapes.length;

	shapeClipboard = selectedShapes.map((shape) => ({
		shape: shape.typeId,
		color: shape.fillColor,
		rotation: shape.group.rotation(),
		scale: shape.group.scaleX() || 1,
		offset: {
			x: shape.group.x() - center.x,
			y: shape.group.y() - center.y,
		},
	}));
}

function pasteClipboardToActiveWorkspace() {
	if (!Array.isArray(shapeClipboard) || shapeClipboard.length === 0) {
		return;
	}

	const sandbox = ensureActiveSandbox();
	if (!sandbox) {
		return;
	}

	const pointer = sandbox.stage.getPointerPosition();
	const basePosition = pointer || { x: sandbox.stage.width() / 2, y: sandbox.stage.height() / 2 };
	const spawnedIds = [];

	shapeClipboard.forEach((entry) => {
		const shape = spawnFromSerializedShape(sandbox, {
			shape: entry.shape,
			color: entry.color,
			rotation: entry.rotation,
			scale: entry.scale,
			position: {
				x: basePosition.x + (entry.offset?.x || 0),
				y: basePosition.y + (entry.offset?.y || 0),
			},
		});
		if (shape) {
			spawnedIds.push(shape.id);
		}
	});

	if (spawnedIds.length > 0) {
		sandbox.setSelectedShapes(spawnedIds);
		sandbox.layer.batchDraw();
		sandbox.notifyShapesChanged();
	}
}

function addSpawnButtons() {
	palette.forEach((shape) => {
		const btn = document.createElement("button");
		btn.type = "button";
		btn.textContent = `+ ${shape.id[0].toUpperCase()}${shape.id.slice(1)}`;
		btn.addEventListener("click", () => {
			const sandbox = ensureActiveSandbox();
			sandbox?.spawnShape(shape);
		});
		controlsEl.appendChild(btn);
	});
}

function updateColorButtonState() {
	const selectedColor = activeSandbox?.getShapeById(activeSandbox.selectedShapeId)?.fillColor || null;
	const enabled = Boolean(activeSandbox?.selectedShapeId);
	colorSwatchButtons.forEach((button) => {
		button.classList.toggle("active", selectedColor === button.dataset.color);
		button.disabled = !enabled;
		button.style.opacity = enabled ? "1" : "0.5";
	});
}

function formatEdgeAnchorDivisionsLabel(divisions) {
	const n = clamp(Number(divisions) || 2, 1, 7);
	if (n === 1) {
		return "none";
	}
	if (n === 2) {
		return "midpoint";
	}
	if (n === 3) {
		return "thirds";
	}
	if (n === 4) {
		return "quarters";
	}
	if (n === 5) {
		return "fifths";
	}
	if (n === 6) {
		return "sixths";
	}
	return "sevenths";
}

function updateEdgeAnchorControlState() {
	if (!edgeAnchorDivisionsInput || !edgeAnchorLabel) {
		return;
	}

	const selectedShapes = activeSandbox?.getSelectedShapes().filter((shape) => !shape.isShadow) || [];
	if (selectedShapes.length === 0) {
		edgeAnchorDivisionsInput.disabled = true;
		edgeAnchorDivisionsInput.value = "2";
		edgeAnchorLabel.textContent = formatEdgeAnchorDivisionsLabel(2);
		return;
	}

	edgeAnchorDivisionsInput.disabled = false;
	const values = selectedShapes.map((shape) => shape.edgeAnchorDivisions || 2);
	const first = values[0];
	const uniform = values.every((value) => value === first);
	if (uniform) {
		edgeAnchorDivisionsInput.value = String(first);
		edgeAnchorLabel.textContent = formatEdgeAnchorDivisionsLabel(first);
	} else {
		edgeAnchorLabel.textContent = "mixed";
	}
}

function addColorButtons() {
	COLOR_CHOICES.forEach((color, index) => {
		const button = document.createElement("button");
		button.type = "button";
		button.className = "color-swatch";
		button.style.background = color;
		const rgb = hexToRgb(color);
		const luminance = 0.2126 * rgb.r + 0.7152 * rgb.g + 0.0722 * rgb.b;
		button.style.color = luminance < 140 ? "#d1d5db" : "#111827";
		button.style.textShadow = luminance < 140 ? "0 1px 2px rgba(0,0,0,0.5)" : "0 1px 1px rgba(255,255,255,0.6)";
		const shortcutLabel = index === 9 ? "0" : String(index + 1);
		button.textContent = shortcutLabel;
		button.dataset.color = color;
		button.dataset.shortcut = shortcutLabel;
		button.setAttribute("aria-label", `Set color ${color} (${shortcutLabel})`);
		button.title = `Key ${shortcutLabel}`;
		button.addEventListener("click", () => {
			const sandbox = ensureActiveSandbox();
			sandbox?.applyColorToSelected(color);
		});
		colorControlsEl.appendChild(button);
		colorSwatchButtons.push(button);
	});
	updateColorButtonState();
}

function getColorIndexFromKeyboardEvent(event) {
	const key = event.key;
	if (key >= "1" && key <= "9") {
		return Number(key) - 1;
	}
	if (key === "0") {
		return 9;
	}
	return -1;
}

function downloadText(filename, content) {
	const blob = new Blob([content], { type: "application/json" });
	const link = document.createElement("a");
	link.href = URL.createObjectURL(blob);
	link.download = filename;
	link.click();
	URL.revokeObjectURL(link.href);
}

async function saveSceneAsFile(content) {
	const suggestedName = "polygon-scene.json";

	if (window.showSaveFilePicker) {
		try {
			const handle = await window.showSaveFilePicker({
				suggestedName,
				types: [
					{
						description: "JSON Files",
						accept: { "application/json": [".json"] },
					},
				],
			});
			const writable = await handle.createWritable();
			await writable.write(content);
			await writable.close();
			return;
		} catch (error) {
			if (error?.name === "AbortError") {
				return;
			}
		}
	}

	let fileName = window.prompt("Save scene as:", suggestedName);
	if (fileName == null) {
		return;
	}
	fileName = fileName.trim();
	if (!fileName) {
		fileName = suggestedName;
	}
	if (!fileName.toLowerCase().endsWith(".json")) {
		fileName += ".json";
	}

	downloadText(fileName, content);
}

function serializeShapeAbsolute(shapeModel) {
	return {
		shape: shapeModel.typeId,
		color: shapeModel.fillColor,
		rotation: shapeModel.group.rotation(),
		scale: shapeModel.group.scaleX() || 1,
		position: {
			x: shapeModel.group.x(),
			y: shapeModel.group.y(),
		},
	};
}

function serializeSandboxShapes(sandbox) {
	if (!sandbox) {
		return [];
	}
	return sandbox.shapes.filter((shape) => !shape.isShadow).map(serializeShapeAbsolute);
}

function getOutputShapesForSceneSave() {
	const original = safeGetLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
	if (original && Array.isArray(original.shapes)) {
		return original.shapes;
	}
	return serializeSandboxShapes(outputSandbox);
}

function serializeAllScene(options = {}) {
	const useOriginalOutputForSave = Boolean(options.useOriginalOutputForSave);
	return {
		version: 2,
		rules: rules.map((rule) => {
			const baseShape = rule.baseSandbox.shapes[0] || null;
			const base = baseShape ? serializeShapeAbsolute(baseShape) : null;
			const basePosition = baseShape
				? { x: baseShape.group.x(), y: baseShape.group.y() }
				: { x: 0, y: 0 };
			const baseScale = baseShape ? baseShape.group.scaleX() || 1 : 1;

			const pattern = rule.patternSandbox.shapes.filter((shapeModel) => !shapeModel.isShadow).map((shapeModel) => ({
				shape: shapeModel.typeId,
				color: shapeModel.fillColor,
				rotation: shapeModel.group.rotation(),
				relativeScale: (shapeModel.group.scaleX() || 1) / baseScale,
				relativePosition: {
					x: shapeModel.group.x() - basePosition.x,
					y: shapeModel.group.y() - basePosition.y,
				},
			}));

			return {
				base,
				pattern,
			};
		}),
		output: {
			shapes: useOriginalOutputForSave
				? getOutputShapesForSceneSave()
				: serializeSandboxShapes(outputSandbox),
		},
	};
}

function safeSetLocalStorage(key, value) {
	try {
		localStorage.setItem(key, JSON.stringify(value));
		return true;
	} catch {
		return false;
	}
}

function safeGetLocalStorage(key) {
	try {
		const raw = localStorage.getItem(key);
		if (!raw) {
			return null;
		}
		return JSON.parse(raw);
	} catch {
		return null;
	}
}

function safeRemoveLocalStorage(key) {
	try {
		localStorage.removeItem(key);
		return true;
	} catch {
		return false;
	}
}

function getSerializedShapeColor(serializedShape) {
	if (!serializedShape || typeof serializedShape !== "object") {
		return DEFAULT_SHAPE_FILL;
	}
	if (typeof serializedShape.color === "string" && serializedShape.color.trim()) {
		return serializedShape.color;
	}
	if (typeof serializedShape.fillColor === "string" && serializedShape.fillColor.trim()) {
		return serializedShape.fillColor;
	}
	return DEFAULT_SHAPE_FILL;
}

function hasValidOutputSnapshot(snapshot) {
	return Boolean(
		snapshot &&
		Array.isArray(snapshot.shapes) &&
		snapshot.shapes.every((shapeData) => typeof getSerializedShapeColor(shapeData) === "string"),
	);
}

function clearApplyRunState() {
	safeRemoveLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
	safeRemoveLocalStorage(STORAGE_RULES_SNAPSHOT_KEY);
}

function clearRulesSnapshotState() {
	safeRemoveLocalStorage(STORAGE_RULES_SNAPSHOT_KEY);
}

function clearOriginalOutputSnapshotState() {
	safeRemoveLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
}

function ensureOriginalOutputSnapshot() {
	if (!outputSandbox) {
		return;
	}
	const existingOriginal = safeGetLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
	if (hasValidOutputSnapshot(existingOriginal)) {
		return;
	}
	safeSetLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY, { shapes: serializeSandboxShapes(outputSandbox) });
}

function rotateVector(vector, radians) {
	const cos = Math.cos(radians);
	const sin = Math.sin(radians);
	return {
		x: vector.x * cos - vector.y * sin,
		y: vector.x * sin + vector.y * cos,
	};
}

function normalizeRotation(degrees) {
	let result = degrees % 360;
	if (result < 0) {
		result += 360;
	}
	return result;
}

function waitMs(ms) {
	return new Promise((resolve) => {
		setTimeout(resolve, ms);
	});
}

function getOutputShapeCount() {
	if (!outputSandbox) {
		return 0;
	}
	return outputSandbox.shapes.filter((shape) => !shape.isShadow).length;
}

function isOutputShapeVisibleEnough(shapeData) {
	if (!shapeData || typeof shapeData !== "object") {
		return false;
	}
	const shapeId = shapeData.shape || shapeData.typeId;
	const shapeConfig = paletteById.get(shapeId);
	if (!shapeConfig) {
		return true;
	}
	const scale = Math.abs(Number(shapeData.scale) || 1);
	return shapeConfig.radius * scale >= MIN_OUTPUT_VISIBLE_RADIUS_PX;
}

function filterVisibleOutputShapes(shapes) {
	if (!Array.isArray(shapes)) {
		return [];
	}
	if (!outputTinyShapesPurged) {
		return shapes.slice();
	}
	return shapes.filter((shapeData) => isOutputShapeVisibleEnough(shapeData));
}

function getPlayMaxShapes() {
	const parsed = Number.parseInt(playMaxShapesInput?.value || "", 10);
	if (!Number.isFinite(parsed) || parsed < 1) {
		return 500;
	}
	return parsed;
}

function getPlayDelayMs() {
	const parsed = Number.parseInt(playDelayMsInput?.value || "", 10);
	if (!Number.isFinite(parsed) || parsed < 0) {
		return 120;
	}
	return Math.max(MIN_PLAY_DELAY_MS, 500 - clamp(parsed, 0, 500));
}

function shouldDisablePlayButton() {
	if (isAutoPlaying) {
		return false;
	}
	if (!playStoppedAtMax) {
		return false;
	}
	return getOutputShapeCount() >= getPlayMaxShapes();
}

function refreshPlayStoppedAtMaxState() {
	if (playStoppedAtMax && getOutputShapeCount() < getPlayMaxShapes()) {
		playStoppedAtMax = false;
	}
}

function updatePlayButtonVisualState() {
	if (!playRulesBtn) {
		return;
	}
	playRulesBtn.textContent = isAutoPlaying ? "■" : "▶";
	playRulesBtn.title = isAutoPlaying ? "Stop play" : "Play iterations";
}

function setOutputActionButtonsEnabled(enabled) {
	const controlsEnabled = enabled && !isAutoPlaying;
	refreshPlayStoppedAtMaxState();
	if (applyRulesBtn) {
		applyRulesBtn.disabled = !controlsEnabled;
	}
	if (resetOutputBtn) {
		resetOutputBtn.disabled = !controlsEnabled;
	}
	if (playMaxShapesInput) {
		playMaxShapesInput.disabled = !controlsEnabled;
	}
	if (playDelayMsInput) {
		playDelayMsInput.disabled = !controlsEnabled;
	}
	if (playRulesBtn) {
		playRulesBtn.disabled = shouldDisablePlayButton();
	}
}

function updateOutputArrowsToggleButton() {
	if (!toggleOutputArrowsBtn) {
		return;
	}
	toggleOutputArrowsBtn.textContent = outputArrowsVisible ? "arrows on" : "arrows off";
	toggleOutputArrowsBtn.title = outputArrowsVisible ? "Hide arrows" : "Show arrows";
	toggleOutputArrowsBtn.setAttribute("aria-pressed", outputArrowsVisible ? "true" : "false");
}

function updateOutputTinyShapesToggleButton() {
	if (!toggleOutputTinyShapesBtn) {
		return;
	}
	toggleOutputTinyShapesBtn.textContent = outputTinyShapesPurged ? "tiny purge on" : "tiny purge off";
	toggleOutputTinyShapesBtn.title = outputTinyShapesPurged ? "Stop purging tiny shapes" : "Purge tiny shapes";
	toggleOutputTinyShapesBtn.setAttribute("aria-pressed", outputTinyShapesPurged ? "true" : "false");
}

function applyTinyShapePurgeToOutputSandbox() {
	if (!outputSandbox || !outputTinyShapesPurged) {
		return;
	}
	const shapesToDelete = outputSandbox.shapes
		.filter((shape) => !shape.isShadow)
		.filter((shape) => !isOutputShapeVisibleEnough(serializeShapeAbsolute(shape)));
	shapesToDelete.forEach((shape) => {
		outputSandbox.deleteShapeById(shape.id);
	});
	outputSandbox.layer.batchDraw();
}

function setOutputTinyShapesPurged(enabled) {
	outputTinyShapesPurged = Boolean(enabled);
	updateOutputTinyShapesToggleButton();
	applyTinyShapePurgeToOutputSandbox();
}

function setOutputArrowsVisible(visible) {
	outputArrowsVisible = Boolean(visible);
	if (outputSandbox) {
		outputSandbox.shapes.forEach((shape) => {
			shape.orientationArrow?.visible(outputArrowsVisible);
		});
		outputSandbox.layer.batchDraw();
	}
	updateOutputArrowsToggleButton();
}

function normalizeColorForMatch(color) {
	if (typeof color !== "string") {
		return "";
	}
	return color.trim().toLowerCase();
}

function getRandomMatchingRule(outputShape, rulesWithBase) {
	const outputShapeId = outputShape?.shape || outputShape?.typeId || "";
	const outputColor = normalizeColorForMatch(outputShape?.color);
	const exactMatches = rulesWithBase.filter(
		(rule) => {
			const ruleShapeId = rule?.base?.shape || rule?.base?.typeId || "";
			if (ruleShapeId !== outputShapeId) {
				return false;
			}
			return normalizeColorForMatch(rule?.base?.color) === outputColor;
		},
	);
	if (exactMatches.length > 0) {
		return exactMatches[Math.floor(Math.random() * exactMatches.length)];
	}
	return null;
}

function transformOutputShapeByRules(outputShape, rulesWithBase, matchedRule = null) {
	let rule = matchedRule;
	if (!rule) {
		rule = getRandomMatchingRule(outputShape, rulesWithBase);
	}

	if (!rule) {
		return [outputShape];
	}

	const transformedShapes = [];
	const baseRotation = Number(rule.base.rotation) || 0;
	const baseScale = Number(rule.base.scale) || 1;
	const outputRotation = Number(outputShape.rotation) || 0;
	const outputScale = Number(outputShape.scale) || 1;
	const deltaDeg = outputRotation - baseRotation;
	const deltaRad = degToRad(deltaDeg);
	const positionScaleRatio = outputScale / baseScale;
	const outputPosition = outputShape.position || { x: 0, y: 0 };

	for (const patternShape of rule.pattern) {
		const rel = patternShape.relativePosition || { x: 0, y: 0 };
		const relScaled = {
			x: (Number(rel.x) || 0) * positionScaleRatio,
			y: (Number(rel.y) || 0) * positionScaleRatio,
		};
		const rotatedRel = rotateVector(relScaled, deltaRad);

		transformedShapes.push({
			shape: patternShape.shape,
			color: patternShape.color,
			rotation: normalizeRotation((Number(patternShape.rotation) || 0) + deltaDeg),
			scale: (Number(patternShape.relativeScale) || 1) * outputScale,
			position: {
				x: (Number(outputPosition.x) || 0) + rotatedRel.x,
				y: (Number(outputPosition.y) || 0) + rotatedRel.y,
			},
		});
	}

	return transformedShapes;
}

function buildOutputFromRules(sceneSnapshot) {
	if (!sceneSnapshot || !Array.isArray(sceneSnapshot.rules) || !sceneSnapshot.output) {
		return null;
	}

	const rulesWithBase = sceneSnapshot.rules.filter(
		(rule) => rule && rule.base && (rule.base.shape || rule.base.typeId) && Array.isArray(rule.pattern),
	);

	const sourceOutputShapes = Array.isArray(sceneSnapshot.output.shapes) ? sceneSnapshot.output.shapes : [];
	const nextOutputShapes = [];

	for (const outputShape of sourceOutputShapes) {
		nextOutputShapes.push(...transformOutputShapeByRules(outputShape, rulesWithBase));
	}

	return filterVisibleOutputShapes(nextOutputShapes);
}

async function applyRulesToOutput() {
	if (!outputSandbox) {
		return;
	}
	if (isApplyingRules) {
		return;
	}

	isApplyingRules = true;
	setOutputActionButtonsEnabled(false);

	try {
		const sceneSnapshot = serializeAllScene();
		if (!isAutoPlaying) {
			ensureOriginalOutputSnapshot();
		}

		safeSetLocalStorage(STORAGE_RULES_SNAPSHOT_KEY, sceneSnapshot);

		if (!sceneSnapshot || !Array.isArray(sceneSnapshot.rules) || !sceneSnapshot.output) {
			return;
		}

		// Transform all shapes in JSON
		const transformedShapes = buildOutputFromRules(sceneSnapshot);
		if (!transformedShapes) {
			return;
		}

		// Bulk clear and reload
		outputSandbox.clearAllShapes();
		transformedShapes.forEach((shapeData) => {
			spawnFromSerializedShape(outputSandbox, shapeData, {
				isReadOnly: true,
				hideOutline: true,
				showOrientationArrow: outputArrowsVisible,
				wrapPosition: true,
			});
		});
		applyTinyShapePurgeToOutputSandbox();
		outputSandbox.resetZoom();
		outputSandbox.layer.batchDraw();
		outputSandbox.notifyShapesChanged();
	} finally {
		isApplyingRules = false;
		setOutputActionButtonsEnabled(true);
	}
}

async function playRulesToLimit() {
	if (!outputSandbox || isAutoPlaying) {
		return;
	}

	ensureOriginalOutputSnapshot();

	playStoppedAtMax = false;
	isAutoPlaying = true;
	autoPlayRunToken += 1;
	const runToken = autoPlayRunToken;
	updatePlayButtonVisualState();
	setOutputActionButtonsEnabled(true);
	outputSandbox.resetZoom();

	try {
		let stoppedByMax = false;
		while (isAutoPlaying && runToken === autoPlayRunToken) {
			const maxShapes = getPlayMaxShapes();
			const beforeCount = getOutputShapeCount();
			if (beforeCount > maxShapes) {
				stoppedByMax = true;
				break;
			}

			await applyRulesToOutput();
			const afterCount = getOutputShapeCount();

			if (afterCount > maxShapes) {
				stoppedByMax = true;
				break;
			}

			const delayMs = getPlayDelayMs();
			if (delayMs > 0) {
				await waitMs(delayMs);
			}
		}
		playStoppedAtMax = stoppedByMax;
	} finally {
		isAutoPlaying = false;
		updatePlayButtonVisualState();
		setOutputActionButtonsEnabled(true);
	}
}

function togglePlayRules() {
	if (shouldDisablePlayButton()) {
		return;
	}

	if (isAutoPlaying) {
		isAutoPlaying = false;
		playStoppedAtMax = false;
		autoPlayRunToken += 1;
		updatePlayButtonVisualState();
		setOutputActionButtonsEnabled(true);
		return;
	}
	playRulesToLimit();
}

function resetOutputFromStorage() {
	if (!outputSandbox) {
		return;
	}
	if (isApplyingRules) {
		return;
	}

	const original = safeGetLocalStorage(STORAGE_OUTPUT_ORIGINAL_KEY);
	if (!original || !Array.isArray(original.shapes)) {
		return;
	}

	isResettingOutput = true;
	try {
		outputSandbox.clearAllShapes();
		filterVisibleOutputShapes(original.shapes).forEach((shapeData) => {
			spawnFromSerializedShape(outputSandbox, shapeData, {
				isReadOnly: false,
				hideOutline: true,
				showOrientationArrow: outputArrowsVisible,
				wrapPosition: true,
			});
		});
		applyTinyShapePurgeToOutputSandbox();
		outputSandbox.resetZoom();
		outputSandbox.layer.batchDraw();
		outputSandbox.notifyShapesChanged();
		setActiveSandbox(outputSandbox);
		playStoppedAtMax = false;
		setOutputActionButtonsEnabled(true);
	} finally {
		isResettingOutput = false;
	}
}

function removeSandbox(sandbox) {
	const index = sandboxes.indexOf(sandbox);
	if (index >= 0) {
		sandboxes.splice(index, 1);
	}
	if (activeSandbox === sandbox) {
		activeSandbox = null;
	}
	sandbox.stage.destroy();
}

function removeLastRule() {
	if (rules.length <= 1) {
		return;
	}

	const rule = rules.pop();
	removeSandbox(rule.baseSandbox);
	removeSandbox(rule.patternSandbox);
	rule.cardEl.remove();
	ruleCount = rules.length;
	updateRuleButtons();

	if (!activeSandbox && rules.length > 0) {
		setActiveSandbox(rules[0].baseSandbox);
	}
}

function removeRule(rule) {
	const index = rules.indexOf(rule);
	if (index < 0 || rules.length <= 1) {
		return;
	}

	rules.splice(index, 1);
	removeSandbox(rule.baseSandbox);
	removeSandbox(rule.patternSandbox);
	rule.cardEl.remove();
	ruleCount = rules.length;
	updateRuleButtons();

	if (!activeSandbox && rules.length > 0) {
		setActiveSandbox(rules[0].baseSandbox);
	}
}

function moveRule(rule, direction) {
	const fromIndex = rules.indexOf(rule);
	if (fromIndex < 0) {
		return;
	}
	const toIndex = fromIndex + direction;
	if (toIndex < 0 || toIndex >= rules.length) {
		return;
	}

	[rules[fromIndex], rules[toIndex]] = [rules[toIndex], rules[fromIndex]];

	if (rulesContainerEl) {
		rules.forEach((ruleModel) => {
			rulesContainerEl.appendChild(ruleModel.cardEl);
		});
	}

	updateRuleButtons();
}

function reorderRulesInDom() {
	if (!rulesContainerEl) {
		return;
	}
	rules.forEach((ruleModel) => {
		rulesContainerEl.appendChild(ruleModel.cardEl);
	});
}

function moveRuleToIndex(rule, toIndex) {
	const fromIndex = rules.indexOf(rule);
	if (fromIndex < 0) {
		return;
	}
	const clampedToIndex = clamp(toIndex, 0, rules.length - 1);
	if (clampedToIndex === fromIndex) {
		return;
	}

	const [moved] = rules.splice(fromIndex, 1);
	rules.splice(clampedToIndex, 0, moved);
	reorderRulesInDom();
	updateRuleButtons();
}

function duplicateRule(rule) {
	const sourceIndex = rules.indexOf(rule);
	if (sourceIndex < 0) {
		return;
	}

	const sourceBaseShape = rule.baseSandbox.shapes.find((shape) => !shape.isShadow) || null;
	const sourceBase = sourceBaseShape ? serializeShapeAbsolute(sourceBaseShape) : null;
	const sourceBasePosition = sourceBaseShape
		? { x: sourceBaseShape.group.x(), y: sourceBaseShape.group.y() }
		: { x: 0, y: 0 };
	const sourceBaseScale = sourceBaseShape ? sourceBaseShape.group.scaleX() || 1 : 1;
	const sourcePattern = rule.patternSandbox.shapes
		.filter((shapeModel) => !shapeModel.isShadow)
		.map((shapeModel) => ({
			shape: shapeModel.typeId,
			color: shapeModel.fillColor,
			rotation: shapeModel.group.rotation(),
			relativeScale: (shapeModel.group.scaleX() || 1) / sourceBaseScale,
			relativePosition: {
				x: shapeModel.group.x() - sourceBasePosition.x,
				y: shapeModel.group.y() - sourceBasePosition.y,
			},
		}));

	const card = createRuleCard();
	const duplicatedRule = rules[rules.length - 1] || null;
	if (!duplicatedRule) {
		return;
	}

	duplicatedRule.baseSandbox.clearAllShapes();
	duplicatedRule.patternSandbox.clearAllShapes();

	if (sourceBase) {
		spawnFromSerializedShape(duplicatedRule.baseSandbox, sourceBase);
	}

	const duplicatedBaseShape = duplicatedRule.baseSandbox.shapes.find((shape) => !shape.isShadow) || null;
	const duplicatedBasePosition = duplicatedBaseShape
		? { x: duplicatedBaseShape.group.x(), y: duplicatedBaseShape.group.y() }
		: { x: 0, y: 0 };
	const duplicatedBaseScale = duplicatedBaseShape ? duplicatedBaseShape.group.scaleX() || 1 : 1;

	sourcePattern.forEach((shapeData) => {
		const rel = shapeData.relativePosition || { x: 0, y: 0 };
		spawnFromSerializedShape(duplicatedRule.patternSandbox, shapeData, {
			x: duplicatedBasePosition.x + Number(rel.x || 0),
			y: duplicatedBasePosition.y + Number(rel.y || 0),
			scale: duplicatedBaseScale * (Number(shapeData.relativeScale) || 1),
		});
	});

	syncRuleBaseShadow(duplicatedRule);

	while (rules.indexOf(duplicatedRule) > sourceIndex + 1) {
		moveRule(duplicatedRule, -1);
	}

	setActiveSandbox(duplicatedRule.baseSandbox);
	requestAnimationFrame(() => {
		card?.scrollIntoView({ behavior: "smooth", block: "center" });
	});
}

function updateRuleButtons() {
	rules.forEach((rule, index) => {
		if (!rule.removeBtnEl) {
			const removeButton = document.createElement("button");
			removeButton.type = "button";
			removeButton.className = "rule-remove-btn";
			removeButton.textContent = "x";
			removeButton.setAttribute("aria-label", "Remove rule");
			removeButton.addEventListener("click", () => {
				removeRule(rule);
			});
			rule.removeBtnEl = removeButton;
		}
		rule.removeBtnEl.disabled = rules.length <= 1;

		if (!rule.moveUpBtnEl) {
			const moveUpButton = document.createElement("button");
			moveUpButton.type = "button";
			moveUpButton.className = "rule-move-btn rule-move-up-btn";
			moveUpButton.textContent = "↑";
			moveUpButton.setAttribute("aria-label", "Move rule up");
			moveUpButton.addEventListener("click", () => {
				moveRule(rule, -1);
			});
			rule.moveUpBtnEl = moveUpButton;
		}

		if (!rule.moveDownBtnEl) {
			const moveDownButton = document.createElement("button");
			moveDownButton.type = "button";
			moveDownButton.className = "rule-move-btn rule-move-down-btn";
			moveDownButton.textContent = "↓";
			moveDownButton.setAttribute("aria-label", "Move rule down");
			moveDownButton.addEventListener("click", () => {
				moveRule(rule, 1);
			});
			rule.moveDownBtnEl = moveDownButton;
		}

		if (!rule.duplicateBtnEl) {
			const duplicateButton = document.createElement("button");
			duplicateButton.type = "button";
			duplicateButton.className = "rule-duplicate-btn";
			duplicateButton.textContent = "⧉";
			duplicateButton.setAttribute("aria-label", "Duplicate rule");
			duplicateButton.addEventListener("click", () => {
				duplicateRule(rule);
			});
			rule.duplicateBtnEl = duplicateButton;
		}

		if (!rule.dragHandleBtnEl) {
			const dragHandleButton = document.createElement("button");
			dragHandleButton.type = "button";
			dragHandleButton.className = "rule-drag-handle-btn";
			dragHandleButton.textContent = "↕";
			dragHandleButton.setAttribute("aria-label", "Drag to reorder rule");
			dragHandleButton.draggable = true;
			dragHandleButton.addEventListener("dragstart", (event) => {
				draggingRule = rule;
				rule.cardEl.classList.add("rule-dragging");
				if (event.dataTransfer) {
					event.dataTransfer.effectAllowed = "move";
					event.dataTransfer.setData("text/plain", "rule-reorder");
				}
			});
			dragHandleButton.addEventListener("dragend", () => {
				rule.cardEl.classList.remove("rule-dragging");
				rules.forEach((r) => r.cardEl.classList.remove("rule-drop-target"));
				draggingRule = null;
			});
			rule.dragHandleBtnEl = dragHandleButton;
		}

		rule.moveUpBtnEl.disabled = index === 0;
		rule.moveDownBtnEl.disabled = index === rules.length - 1;
		rule.cardEl.appendChild(rule.dragHandleBtnEl);
		rule.cardEl.appendChild(rule.duplicateBtnEl);
		rule.cardEl.appendChild(rule.moveUpBtnEl);
		rule.cardEl.appendChild(rule.moveDownBtnEl);
		rule.cardEl.appendChild(rule.removeBtnEl);
	});

	if (rulesContainerEl) {
		rulesContainerEl.prepend(addRuleButtonEl);
	}
}

function ensureRuleCount(count) {
	const targetCount = Math.max(1, count);
	while (rules.length < targetCount) {
		createRuleCard();
	}
	while (rules.length > targetCount) {
		removeLastRule();
	}
}

function spawnFromSerializedShape(sandbox, serializedShape, options = {}) {
	if (!serializedShape || typeof serializedShape !== "object") {
		return null;
	}

	const shapeId = serializedShape.shape || serializedShape.typeId;
	const shapeConfig = paletteById.get(shapeId);
	if (!shapeConfig) {
		return null;
	}

	const position = serializedShape.position || {};
	const resolvedX = Number(options.x ?? position.x);
	const resolvedY = Number(options.y ?? position.y);
	const spawnOptions = {
		rotation: Number(serializedShape.rotation) || 0,
		scale: Number.isFinite(Number(options.scale))
			? Number(options.scale)
			: Number(serializedShape.scale) || 1,
		fillColor: getSerializedShapeColor(serializedShape),
		isReadOnly: Boolean(options.isReadOnly),
		hideOutline: Boolean(options.hideOutline),
		showOrientationArrow: options.showOrientationArrow !== false,
		wrapPosition: Boolean(options.wrapPosition),
	};

	if (Number.isFinite(resolvedX)) {
		spawnOptions.x = resolvedX;
	}
	if (Number.isFinite(resolvedY)) {
		spawnOptions.y = resolvedY;
	}

	return sandbox.spawnShape(shapeConfig, spawnOptions);
}

function syncRuleBaseShadow(rule) {
	if (!rule || !rule.baseSandbox || !rule.patternSandbox) {
		return;
	}

	const baseShape = rule.baseSandbox.shapes.find((shape) => !shape.isShadow) || null;
	let shadowShape = rule.patternSandbox.shapes.find((shape) => shape.isShadow && shape.shadowKind === "base-shadow") || null;
	const baseEdgeDivisions = Number(baseShape?.edgeAnchorDivisions) || 2;

	if (!baseShape) {
		if (shadowShape) {
			rule.patternSandbox.deleteShapeById(shadowShape.id);
		}
		return;
	}

	if (
		!shadowShape ||
		shadowShape.typeId !== baseShape.typeId ||
		(Number(shadowShape.edgeAnchorDivisions) || 2) !== baseEdgeDivisions
	) {
		if (shadowShape) {
			rule.patternSandbox.deleteShapeById(shadowShape.id);
		}

		shadowShape = rule.patternSandbox.spawnShape(paletteById.get(baseShape.typeId), {
			x: baseShape.group.x(),
			y: baseShape.group.y(),
			rotation: baseShape.group.rotation(),
			scale: baseShape.group.scaleX() || 1,
			edgeAnchorDivisions: baseEdgeDivisions,
			fillColor: baseShape.fillColor,
			isShadow: true,
			shadowKind: "base-shadow",
		});
		if (!shadowShape) {
			return;
		}
	}

	rule.patternSandbox.setShapeColor(shadowShape, baseShape.fillColor);
	shadowShape.group.position({ x: baseShape.group.x(), y: baseShape.group.y() });
	shadowShape.group.rotation(baseShape.group.rotation());
	const baseScale = baseShape.group.scaleX() || 1;
	shadowShape.group.scaleX(baseScale);
	shadowShape.group.scaleY(baseScale);
	rule.patternSandbox.updateShapeMarkerVisuals(shadowShape, false);
	shadowShape.group.moveToBottom();
	rule.patternSandbox.layer.batchDraw();
}

function getRuleByBaseSandbox(sandbox) {
	return rules.find((rule) => rule.baseSandbox === sandbox) || null;
}

function loadAllSceneData(sceneData) {
	if (!sceneData || !Array.isArray(sceneData.rules) || !sceneData.output || !Array.isArray(sceneData.output.shapes)) {
		throw new Error("Invalid scene format.");
	}

	// Ensure stale autoplay/max-stop state never survives a scene load.
	isAutoPlaying = false;
	playStoppedAtMax = false;
	autoPlayRunToken += 1;
	updatePlayButtonVisualState();

	clearApplyRunState();

	ensureRuleCount(sceneData.rules.length);

	rules.forEach((rule) => {
		rule.baseSandbox.clearAllShapes();
		rule.patternSandbox.clearAllShapes();
	});

	sceneData.rules.forEach((ruleData, ruleIndex) => {
		const rule = rules[ruleIndex];
		if (!rule) {
			return;
		}

		if (ruleData.base) {
			spawnFromSerializedShape(rule.baseSandbox, ruleData.base);
		}

		const baseShape = rule.baseSandbox.shapes[0] || null;
		if (ruleData.base && !baseShape) {
			syncRuleBaseShadow(rule);
			return;
		}

		const basePosition = baseShape
			? { x: baseShape.group.x(), y: baseShape.group.y() }
			: { x: 0, y: 0 };
		const baseScale = baseShape ? baseShape.group.scaleX() || 1 : 1;

		if (Array.isArray(ruleData.pattern)) {
			ruleData.pattern.forEach((shapeData) => {
				const rel = shapeData.relativePosition || { x: 0, y: 0 };
				const relativeScale = Number(shapeData.relativeScale) || 1;
				spawnFromSerializedShape(rule.patternSandbox, shapeData, {
					x: basePosition.x + Number(rel.x || 0),
					y: basePosition.y + Number(rel.y || 0),
					scale: baseScale * relativeScale,
				});
			});
		}

		syncRuleBaseShadow(rule);
	});

	if (outputSandbox) {
		outputSandbox.clearAllShapes();
		filterVisibleOutputShapes(sceneData.output.shapes).forEach((shapeData) => {
			spawnFromSerializedShape(outputSandbox, shapeData, {
				hideOutline: true,
				showOrientationArrow: outputArrowsVisible,
				wrapPosition: true,
			});
		});
		applyTinyShapePurgeToOutputSandbox();
	}

	if (rules[0]) {
		setActiveSandbox(rules[0].baseSandbox);
	}

	setOutputActionButtonsEnabled(true);
}

function createRuleCard() {
	ruleCount += 1;
	const card = document.createElement("article");
	card.className = "rule-card";

	const workspaces = document.createElement("div");
	workspaces.className = "rule-workspaces";
	const workspaceElements = [];

	for (let i = 0; i < WORKSPACES_PER_RULE; i += 1) {
		const workspace = document.createElement("div");
		workspace.className = "workspace";
		workspaces.appendChild(workspace);
		workspaceElements.push({ workspace, workspaceIndex: i });
	}

	card.appendChild(workspaces);
	rulesContainerEl.appendChild(card);

	let baseSandbox = null;
	let patternSandbox = null;

	for (const entry of workspaceElements) {
		const isBaseWorkspace = entry.workspaceIndex === 0;
		const sandbox = new Sandbox(entry.workspace, {
			maxShapes: isBaseWorkspace ? 1 : Infinity,
		});
		sandbox.resize();
		sandboxes.push(sandbox);
		if (entry.workspaceIndex === 0) {
			baseSandbox = sandbox;
		} else {
			patternSandbox = sandbox;
		}
		entry.workspace.addEventListener("pointerdown", () => setActiveSandbox(sandbox));
	}

	const ruleModel = {
		cardEl: card,
		baseSandbox,
		patternSandbox,
		removeBtnEl: null,
		dragHandleBtnEl: null,
		duplicateBtnEl: null,
		moveUpBtnEl: null,
		moveDownBtnEl: null,
	};
	rules.push(ruleModel);

	card.addEventListener("dragover", (event) => {
		if (!draggingRule || draggingRule === ruleModel) {
			return;
		}
		event.preventDefault();
		card.classList.add("rule-drop-target");
	});

	card.addEventListener("dragleave", () => {
		card.classList.remove("rule-drop-target");
	});

	card.addEventListener("drop", (event) => {
		if (!draggingRule || draggingRule === ruleModel) {
			return;
		}
		event.preventDefault();
		card.classList.remove("rule-drop-target");
		const targetIndex = rules.indexOf(ruleModel);
		moveRuleToIndex(draggingRule, targetIndex);
	});

	baseSandbox.setShapesChangedHandler(() => {
		syncRuleBaseShadow(ruleModel);
		if (!isApplyingRules && !isAutoPlaying) {
			clearRulesSnapshotState();
		}
	});
	patternSandbox.setShapesChangedHandler(() => {
		if (!isApplyingRules && !isAutoPlaying) {
			clearRulesSnapshotState();
		}
	});
	syncRuleBaseShadow(ruleModel);
	updateRuleButtons();

	if (!activeSandbox && sandboxes[0]) {
		setActiveSandbox(sandboxes[0]);
	}

	return card;
}

async function handleLoadFile(event) {
	const [file] = event.target.files || [];
	if (!file) {
		return;
	}
	try {
		const text = await file.text();
		loadAllSceneData(JSON.parse(text));
	} catch {
		// Ignore invalid scene files silently.
	}
	loadInput.value = "";
}

addSpawnButtons();
addColorButtons();
updateEdgeAnchorControlState();
addRuleButtonEl.type = "button";
addRuleButtonEl.className = "add-rule-btn rules-add-btn";
addRuleButtonEl.textContent = "+";
addRuleButtonEl.setAttribute("aria-label", "Add another rule");
addRuleButtonEl.addEventListener("click", () => {
	const card = createRuleCard();
	const newestRule = rules[rules.length - 1] || null;
	if (newestRule?.baseSandbox) {
		setActiveSandbox(newestRule.baseSandbox);
	}
	requestAnimationFrame(() => {
		card?.scrollIntoView({ behavior: "smooth", block: "center" });
	});
});
createRuleCard();
// Prevent stale data from previous browser sessions affecting reset/apply behavior.
clearApplyRunState();

if (outputWorkspaceEl) {
	outputSandbox = new Sandbox(outputWorkspaceEl, { enableZoom: true });
	outputSandbox.resize();
	sandboxes.push(outputSandbox);
	outputSandbox.setShapesChangedHandler(() => {
		if (!isApplyingRules && !isAutoPlaying && !isResettingOutput) {
			clearOriginalOutputSnapshotState();
		}
	});
}

clearBtn.addEventListener("click", () => {
	ensureActiveSandbox()?.clearAllShapes({ preserveShadows: true });
});

clearAllBtn?.addEventListener("click", () => {
	while (rules.length > 1) {
		removeLastRule();
	}
	rules[0]?.baseSandbox.clearAllShapes();
	rules[0]?.patternSandbox.clearAllShapes();
	outputSandbox?.clearAllShapes();
	isAutoPlaying = false;
	playStoppedAtMax = false;
	autoPlayRunToken += 1;
	updatePlayButtonVisualState();
	setOutputActionButtonsEnabled(true);
	clearApplyRunState();
});

rotateLeftBtn.addEventListener("click", () => {
	const sandbox = ensureActiveSandbox();
	sandbox?.rotateSelected(-getRotateStepDegrees(sandbox));
});

rotateRightBtn.addEventListener("click", () => {
	const sandbox = ensureActiveSandbox();
	sandbox?.rotateSelected(getRotateStepDegrees(sandbox));
});

scaleDownBtn?.addEventListener("click", () => {
	ensureActiveSandbox()?.scaleSelected(SCALE_STEP_DOWN);
});

scaleUpBtn?.addEventListener("click", () => {
	ensureActiveSandbox()?.scaleSelected(SCALE_STEP_UP);
});

edgeAnchorDivisionsInput?.addEventListener("input", () => {
	const divisions = Number.parseInt(edgeAnchorDivisionsInput.value, 10);
	const sandbox = ensureActiveSandbox();
	if (!sandbox || !Number.isFinite(divisions)) {
		return;
	}
	sandbox.setEdgeAnchorsForSelected(divisions);
	edgeAnchorLabel.textContent = formatEdgeAnchorDivisionsLabel(divisions);
});

playMaxShapesInput?.addEventListener("input", () => {
	setOutputActionButtonsEnabled(true);
});

window.addEventListener("keydown", (event) => {
	const target = event.target;
	if (target instanceof HTMLElement) {
		const tag = target.tagName;
		if (tag === "INPUT" || tag === "TEXTAREA" || target.isContentEditable) {
			return;
		}
	}

	const sandbox = ensureActiveSandbox();

	const key = event.key.toLowerCase();
	if (key === "q" || key === "e") {
		if (!sandbox) {
			return;
		}
		event.preventDefault();
		const step = getRotateStepDegrees(sandbox);
		sandbox.rotateSelected(key === "q" ? -step : step);
		return;
	}

	if (event.key === "Backspace" || event.key === "Delete") {
		if (!sandbox) {
			return;
		}
		event.preventDefault();
		sandbox.deleteSelected();
		return;
	}

	const colorIndex = getColorIndexFromKeyboardEvent(event);
	if (colorIndex < 0 || colorIndex >= COLOR_CHOICES.length) {
		return;
	}

	if (!sandbox?.selectedShapeId) {
		return;
	}

	event.preventDefault();
	sandbox.applyColorToSelected(COLOR_CHOICES[colorIndex]);
});

saveBtn.addEventListener("click", async () => {
	const content = JSON.stringify(serializeAllScene({ useOriginalOutputForSave: true }), null, 2);
	await saveSceneAsFile(content);
});

loadBtn.addEventListener("click", () => loadInput.click());
loadInput.addEventListener("change", handleLoadFile);
applyRulesBtn?.addEventListener("click", applyRulesToOutput);
resetOutputBtn?.addEventListener("click", resetOutputFromStorage);
playRulesBtn?.addEventListener("click", togglePlayRules);
toggleOutputArrowsBtn?.addEventListener("click", () => {
	setOutputArrowsVisible(!outputArrowsVisible);
});
toggleOutputTinyShapesBtn?.addEventListener("click", () => {
	setOutputTinyShapesPurged(!outputTinyShapesPurged);
});
updatePlayButtonVisualState();
updateOutputArrowsToggleButton();
updateOutputTinyShapesToggleButton();
setOutputActionButtonsEnabled(true);

window.addEventListener("resize", () => {
	for (const sandbox of sandboxes) {
		sandbox.resize();
	}
});

window.addEventListener("keydown", (event) => {
	if (!(event.ctrlKey || event.metaKey)) {
		return;
	}

	const key = event.key.toLowerCase();
	if (key === "c") {
		event.preventDefault();
		copySelectionToClipboard();
		return;
	}

	if (key === "v") {
		event.preventDefault();
		pasteClipboardToActiveWorkspace();
	}
});
